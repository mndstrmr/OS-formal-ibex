import ObservationalCorrectness.InfList

---- Ibex
structure IbexIns (v : Type u) where
  gnt_i : Bool -- Not actually an output but I don't think it matters? Outputs are a function of inputs anyway

structure CombIn (μ v : Type u) where
  state : μ
  inputs : IbexIns v

structure IbexOuts (v : Type u) where
  data_req_o : Bool
  data_wdata_o_mask : v
  data_be_o : v
  data_we_o : Bool
  data_addr_o : v
  ins : IbexIns v -- for convenience

structure Ibex (μ v : Type u) where
  step : CombIn μ v -> μ
  outputs : CombIn μ v -> IbexOuts v
  init : μ

axiom IbexOutsInsCopy (ibex : Ibex μ v) (s : CombIn μ v) : (ibex.outputs s).ins = s.inputs

def Ibex.run (ibex : Ibex μ v) (seq : List (IbexIns v)) : μ :=
  seq.foldl (fun s i => ibex.step { state := s, inputs := i }) ibex.init

def Ibex.seq (ibex : Ibex μ v) (is : InfList (IbexIns v)) : InfList μ :=
  is.inits.map fun is => ibex.run is

def Ibex.reachable (ibex : Ibex μ v) (s : μ) : Prop :=
  ∃ (is : List (IbexIns v)), ibex.run is = s


---- Specification
@[ext]
structure RestrictedAbsState (v r : Type u) where
  csrs : v
  ra : Option v
  rb : Option v

@[ext]
structure AbsState (v r : Type u) where
  csrs : v
  regfile : r -> v

inductive AbsMemOp (v : Type u) where
| read : v -> AbsMemOp v -- addr
| write : v -> v -> v -> AbsMemOp v -- addr, data, mask

def IbexOuts.interpret (o : IbexOuts v) : List (AbsMemOp v) :=
  if o.ins.gnt_i then
    if o.data_we_o then [.write o.data_addr_o o.data_wdata_o_mask o.data_be_o]
    else [.read o.data_addr_o]
  else []
theorem IbexOuts.interpret_len (o : IbexOuts v) : o.interpret.length = if o.ins.gnt_i then 1 else 0 := by
  simp [IbexOuts.interpret]
  cases o.ins.gnt_i
  simp
  cases o.data_we_o
  simp
  simp


structure Spec (v r i : Type u) where
  ra : i -> Option r
  rb : i -> Option r
  step : AbsState v r -> i -> AbsState v r
  routputs : RestrictedAbsState v r -> i -> List (AbsMemOp v)
  init : AbsState v r

def AbsState.restrict (a : AbsState v r) (spec : Spec v r i) (x : i) : RestrictedAbsState v r :=
  { csrs := a.csrs, ra := (spec.ra x).map a.regfile, rb := (spec.rb x).map a.regfile }

def Spec.outputs (spec : Spec v r i) (a : AbsState v r) (input : i) : List (AbsMemOp v) := spec.routputs (a.restrict spec input) input

def Spec.run (spec : Spec v r i) (is : List i) : AbsState v r :=
  is.foldl (fun s i => spec.step s i) spec.init

def Spec.seq (s : Spec v r i) (is : InfList i) : InfList (AbsState v r) :=
  is.inits.map fun is => s.run is

axiom SpecOutTypes (s : Spec v r i) (a : AbsState v r) (x : i) : match s.outputs a x with
| [] => True
| [_] => True
| [.read _, .read _] => True
| [.write _ _ _, .write _ _ _] => True
| _ => False

theorem SpecOutLimit (s : Spec v r i) (a : AbsState v r) (x : i) : (s.outputs a x).length ≤ 2 := by
  match h : s.outputs a x with
  | [] => simp [List.length]
  | [_] => simp [List.length]
  | [_, _] => rfl
  | _ :: _ :: _ :: _ =>
    have t := SpecOutTypes s a x
    simp [h] at t

----- Verif
structure Verif {αi μ va r : Type u}  where
  ibex : Ibex μ va
  spec : Spec va r αi

  abs : CombIn μ va -> RestrictedAbsState va r
  absi : CombIn μ va -> αi

  spec_past : CombIn μ va -> AbsState va r
  has_spec_past : CombIn μ va -> Bool
  spec_past_has_reg : CombIn μ va -> r -> Bool
  -- reg_driven : CombIn μ va -> r -> Bool
  addr_a : CombIn μ va -> r
  addr_b : CombIn μ va -> r
  ren_a : CombIn μ va -> Bool
  ren_b : CombIn μ va -> Bool
  spec_en : CombIn μ va -> Bool
  mem_gnt_fst_q : μ -> Bool
  mem_gnt_snd_q : μ -> Bool

  realise : InfList αi -> InfList (IbexIns va)

def Verif.check (_ : @Verif αi μ va r) (a : List (AbsMemOp va)) (o : List (IbexOuts va)) : Prop :=
  a = (o.map IbexOuts.interpret).flatten

def Verif.sample (v : @Verif αi μ va r) (is : InfList αi) : InfList (CombIn μ va) :=
  ((v.ibex.seq (v.realise is)).zip (v.realise is)).map fun (x, y) => ⟨x, y⟩

def Verif.sample_spec (v : @Verif αi μ va r) (is : InfList αi) : InfList (AbsState va r × αi) :=
  ((v.spec.seq is).zip is).map fun (x, y) => (x, y)

def Verif.addr_a? (v : @Verif αi μ va r) (s : CombIn μ va) := if v.ren_a s then some (v.addr_a s) else none
def Verif.addr_b? (v : @Verif αi μ va r) (s : CombIn μ va) := if v.ren_b s then some (v.addr_b s) else none

def Verif.spec_outs (v : @Verif αi μ va r) (s : CombIn μ va) := v.spec.routputs (v.abs s) (v.absi s)
def Verif.spec_mem_en (v : @Verif αi μ va r) (s : CombIn μ va) := !(v.spec_outs s).isEmpty
def Verif.spec_mem_en_snd (v : @Verif αi μ va r) (s : CombIn μ va) := (v.spec_outs s).length > 1
def Verif.spec_mem_write (v : @Verif αi μ va r) (s : CombIn μ va) := match (v.spec_outs s) with | .write _ _ _ :: _ => True | _ => False
def Verif.spec_mem_read (v : @Verif αi μ va r) (s : CombIn μ va) := match (v.spec_outs s) with | .read _ :: _ => True | _ => False
def Verif.spec_mem_fst_addr (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | .read a :: _ => some a | .write a _ _ :: _ => some a | _ => none
def Verif.spec_mem_snd_addr (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | _ :: .read a :: _ => some a | _ :: .write a _ _ :: _ => some a | _ => none
def Verif.spec_mem_write_fst_wdata_mask (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | .write _ d _ :: _ => some d | _ => none
def Verif.spec_mem_write_snd_wdata_mask (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | _ :: .write _ d _ :: _ => some d | _ => none
def Verif.spec_mem_write_fst_be (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | .write _ _ b :: _ => some b | _ => none
def Verif.spec_mem_write_snd_be (v : @Verif αi μ va r) (s : CombIn μ va) := match v.spec_outs s with | _ :: .write _ _ b :: _ => some b | _ => none


def Verif.mem_gnt_fst_d (v : @Verif αi μ va r) (s : CombIn μ va) : Bool := v.mem_gnt_fst_q s.state ∨ s.inputs.gnt_i
def Verif.mem_gnt_snd_d (v : @Verif αi μ va r) (s : CombIn μ va) : Bool := v.mem_gnt_snd_q s.state ∨ (s.inputs.gnt_i ∧ v.mem_gnt_fst_q s.state)
def Verif.mem_req_fst_d (v : @Verif αi μ va r) (s : CombIn μ va) : Bool := (v.ibex.outputs s).data_req_o ∧ ¬v.mem_gnt_fst_q s.state
def Verif.mem_req_snd_d (v : @Verif αi μ va r) (s : CombIn μ va) : Bool := (v.ibex.outputs s).data_req_o ∧ v.mem_gnt_fst_q s.state

----- Liveness
axiom SpecEnLimit : Nat
axiom SpecEnLiveness (v : @Verif αi μ v r) (is : InfList αi) :
  ∀ (t : Nat), ((v.sample is).drop t).any_within SpecEnLimit (fun m => v.spec_en m)

noncomputable def Verif.kth_spec_en (v : @Verif αi μ va r) (is : InfList αi) (n : Nat) : Nat := (v.sample is).kth_max_sep v.spec_en n (SpecEnLiveness v is)

noncomputable def Verif.sample_en (v : @Verif αi μ va r) (is : InfList αi) : InfList (CombIn μ va) :=
  { get := fun n => (v.sample is).get (v.kth_spec_en is n) }

noncomputable def Verif.spec_en_incl_start (v : @Verif αi μ va r) (is : InfList αi) : Nat -> Nat
| 0 => 0
| .succ n =>
  v.kth_spec_en is n + 1

noncomputable def Verif.spec_en_incl_end (v : @Verif αi μ va r) (is : InfList αi) : Nat -> Nat := fun n => v.kth_spec_en is n

noncomputable def Verif.cumm_outs_to (v : @Verif αi μ va r) (is : InfList αi) (n t : Nat) : List (IbexOuts va) :=
  (((v.sample is).drop (v.spec_en_incl_start is n)).take (t + 1)).val.map v.ibex.outputs

theorem Verif.cumm_outs_to_split (v : @Verif αi μ va r) (is : InfList αi) (n t : Nat) :
  v.cumm_outs_to is n (t + 1) = v.cumm_outs_to is n t ++ [v.ibex.outputs ((v.sample is).get (v.spec_en_incl_start is n + t + 1))]
:= by simp [Verif.cumm_outs_to, InfList.take_map_assoc, InfList.take_add_one, InfList.drop, Nat.add_assoc]

noncomputable def Verif.cumm_outs (v : @Verif αi μ va r) (is : InfList αi) : Nat -> List (IbexOuts va) :=
  fun n => v.cumm_outs_to is n (v.spec_en_incl_end is n - v.spec_en_incl_start is n)

----- Unproven base case:
axiom Initial (v : @Verif αi μ v r) (is : InfList αi) : v.abs (v.sample_en is).head = v.spec.init.restrict v.spec (is.get 0)

------ Axioms forhis proof
axiom HasSpecPast (v : @Verif αi μ va r) (s : CombIn μ va) : v.has_spec_past s
axiom HasSpecPastReg (v : @Verif αi μ va r) (s : CombIn μ va) (r : r) : v.spec_past_has_reg s r

----- Properties of realise
axiom Realise (v : @Verif αi μ v r) (is : InfList αi) (n i : Nat) (h : v.spec_en_incl_start is n ≤ i ∧ i ≤ v.spec_en_incl_end is n) :
  v.absi ((v.sample is).get i) = is.get n
