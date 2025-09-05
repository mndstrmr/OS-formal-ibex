-- These are properties proven, or defined in SV

import ObservationalCorrectness.Verif

axiom MemGntFstQ (v : @Verif αi μ va r) (s : CombIn μ va) : v.mem_gnt_fst_q (v.ibex.step s) = if v.spec_en s then false else v.mem_gnt_fst_d s
axiom MemGntSndQ (v : @Verif αi μ va r) (s : CombIn μ va) : v.mem_gnt_snd_q (v.ibex.step s) = if v.spec_en s then false else v.mem_gnt_snd_d s
axiom MemGntFstInit (v : @Verif αi μ va r) : v.mem_gnt_fst_q v.ibex.init = false
axiom MemGntSndInit (v : @Verif αi μ va r) : v.mem_gnt_snd_q v.ibex.init = false

axiom RegDriven (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) (reg : r) :
  (reg = v.addr_a s -> (v.abs s).ra.isSome = v.ren_a s) ∧
  (reg = v.addr_b s -> (v.abs s).rb.isSome = v.ren_b s)

axiom WrapCsrs (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.has_spec_past s -> (v.abs s).csrs = (v.spec_past s).csrs
axiom WrapRegA (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  (v.abs s).ra.isSome -> v.spec_past_has_reg s (v.addr_a s) -> (v.spec_past s).regfile (v.addr_a s) = (v.abs s).ra
axiom WrapRegB (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  (v.abs s).rb.isSome -> v.spec_past_has_reg s (v.addr_b s) -> (v.spec_past s).regfile (v.addr_b s) = (v.abs s).rb

-- FIXME: This is not an actually verified property! It shouldn't need to be though, because in practice this isn't really how it works.
axiom RAMatch (v : @Verif αi μ va r) (s : CombIn μ va) : v.addr_a? s = v.spec.ra (v.absi s)
axiom RBMatch (v : @Verif αi μ va r) (s : CombIn μ va) : v.addr_b? s = v.spec.rb (v.absi s)

-- This is what is actually written, but it would just be better if it was the second instead, and it would be a small change
-- axiom MemEn (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
--   (v.ibex.outputs s).data_req_o -> v.spec_mem_en s
axiom MemEn' (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_fst_d s -> v.spec_mem_en s
axiom SndEn (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_snd_d s -> v.spec_mem_en_snd s

-- New
axiom MemEnG (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_gnt_fst_d s -> v.spec_mem_en s
axiom SndEnG (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_gnt_snd_d s -> v.spec_mem_en_snd s

axiom We (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  (v.ibex.outputs s).data_req_o -> (v.ibex.outputs s).data_we_o = v.spec_mem_write s ∧ (v.ibex.outputs s).data_we_o = ¬v.spec_mem_read s

axiom FstAddr (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_fst_d s -> v.spec_mem_fst_addr s = (v.ibex.outputs s).data_addr_o
axiom SndAddr (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_snd_d s -> v.spec_mem_snd_addr s = (v.ibex.outputs s).data_addr_o

axiom FstWData (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_fst_d s -> (v.ibex.outputs s).data_we_o -> v.spec_mem_write_fst_wdata_mask s = (v.ibex.outputs s).data_wdata_o_mask
axiom SndWData (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_snd_d s -> (v.ibex.outputs s).data_we_o -> v.spec_mem_write_snd_wdata_mask s = (v.ibex.outputs s).data_wdata_o_mask

-- New
axiom FstBE (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_fst_d s -> (v.ibex.outputs s).data_we_o -> v.spec_mem_write_fst_be s = (v.ibex.outputs s).data_be_o
axiom SndBE (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_req_snd_d s -> (v.ibex.outputs s).data_we_o -> v.spec_mem_write_snd_be s = (v.ibex.outputs s).data_be_o

axiom FstEnd (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.spec_en s -> v.spec_mem_en s -> v.mem_gnt_fst_d s
axiom SndEnd (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.spec_en s -> v.spec_mem_en_snd s -> v.mem_gnt_snd_d s

-- From the memory protocol
axiom GntImpliesReq (ibex : Ibex μ va) (s : CombIn μ va) : s.inputs.gnt_i -> (ibex.outputs s).data_req_o

axiom LSUMaxTwoReqs (v : @Verif αi μ va r) (s : CombIn μ va) (reach : v.ibex.reachable s.state) :
  v.mem_gnt_snd_q s.state -> ¬(v.ibex.outputs s).data_req_o

-- from the definition of spec_past_..., though FIXME: should be derived from definitions
axiom SpecPastStable (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  let i := v.kth_spec_en is n
  let j := v.kth_spec_en is n.succ
  ∀ (t : Nat), (i < t ∧ t ≤ j) -> v.spec_past ((v.sample is).get t) = (v.spec.seq is).get n.succ

-- FIXME: In practice this should be much tighter
-- Also do we really prove this? I'm not sure we do.
axiom SpecStable (v : @Verif αi μ v r) (is : InfList αi) (n i : Nat) (h : v.spec_en_incl_start is n ≤ i ∧ i ≤ v.spec_en_incl_end is n) :
  (v.ibex.outputs ((v.sample is).get i)).data_req_o -> v.abs ((v.sample is).get i) = v.abs ((v.sample_en is).get n)
