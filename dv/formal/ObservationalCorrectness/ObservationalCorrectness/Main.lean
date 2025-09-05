import Mathlib.Tactic
import ObservationalCorrectness.Verif
import ObservationalCorrectness.InfList
import ObservationalCorrectness.ModelChecked

theorem SpecPastEnd (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.spec_past ((v.sample_en is).get (n + 1)) = (v.spec.seq is).get (n + 1) :=
  let i := v.kth_spec_en is n
  let j := v.kth_spec_en is (n + 1)
  have ho : (v.sample_en is).get (n + 1) = (v.sample is).get j := by rw [Verif.sample_en]
  have h1 : i < j := InfList.kth_max_step_diff _ _ _ _
  have h2 : j ≤ j := by simp
  have h := SpecPastStable v is n j (And.intro h1 h2)
  by rw [<-h, ho]

theorem SampledIsReachable (v : @Verif αi μ va r) : v.ibex.reachable ((v.sample is).get n).state := by
  simp [Ibex.reachable, Ibex.run, Verif.sample, InfList.map, InfList.zip, Ibex.seq]

theorem SampleEnIsSpecEn (v : @Verif αi μ va r) : v.spec_en ((v.sample_en is).get n) := by
  let x := (v.sample is).kth_max_sep v.spec_en n (SpecEnLiveness v is)
  exact x.property

theorem start_before_end (v : @Verif αi μ v r) (is : InfList αi) :
  v.spec_en_incl_start is n ≤ v.spec_en_incl_end is n := by match n with
| 0 => simp [Verif.spec_en_incl_start, Verif.spec_en_incl_end]
| n + 1 => exact Nat.lt_iff_add_one_le.mp (InfList.kth_max_step_diff _ _ _ _)

theorem RealiseSpecEn (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.absi ((v.sample_en is).get n) = is.get n := by
  simp [Verif.sample_en]
  exact Realise _ _ _ _ (And.intro (start_before_end _ _) (by simp [Verif.spec_en_incl_end]))

theorem Continuity (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.abs ((v.sample_en is).get n) = ((v.spec.seq is).get n).restrict v.spec (is.get n) :=
  match n with
  | 0 => Initial v is
  | n + 1 => by
      ext : 1
      . rw [
          WrapCsrs v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) (HasSpecPast v _),
          SpecPastEnd v is n,
          AbsState.restrict
        ]
      . if h : (v.addr_a? ((v.sample_en is).get (n + 1))).isSome then
          simp [Verif.addr_a?] at h
          have h2 := RAMatch v ((v.sample_en is).get (n + 1))
          simp [Verif.addr_a?] at h2
          have h3 := (RegDriven v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) (v.addr_a ((v.sample_en is).get (n + 1)))).left
          simp [h] at h3
          simp [h, RealiseSpecEn] at h2
          simp [
            <-WrapRegA v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) h3 (HasSpecPastReg _ _ _),
            SpecPastEnd v is n,
            AbsState.restrict,
            <-h2,
          ]
        else
          simp [Verif.addr_a?] at h
          have h2 := RAMatch v ((v.sample_en is).get (n + 1))
          simp [Verif.addr_a?] at h2
          have h3 := (RegDriven v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) (v.addr_a ((v.sample_en is).get (n + 1)))).left
          simp [h] at h3
          simp [h, RealiseSpecEn] at h2
          simp [AbsState.restrict, <-h2, h3]
      . if h : (v.addr_b? ((v.sample_en is).get (n + 1))).isSome then
          simp [Verif.addr_b?] at h
          have h2 := RBMatch v ((v.sample_en is).get (n + 1))
          simp [Verif.addr_b?] at h2
          have h3 := (RegDriven v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) (v.addr_b ((v.sample_en is).get (n + 1)))).right
          simp [h] at h3
          simp [h, RealiseSpecEn] at h2
          simp [
            <-WrapRegB v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) h3 (HasSpecPastReg _ _ _),
            SpecPastEnd v is n,
            AbsState.restrict,
            <-h2,
          ]
        else
          simp [Verif.addr_b?] at h
          have h2 := RBMatch v ((v.sample_en is).get (n + 1))
          simp [Verif.addr_b?] at h2
          have h3 := (RegDriven v ((v.sample_en is).get (n + 1)) (SampledIsReachable _) (v.addr_b ((v.sample_en is).get (n + 1)))).right
          simp [h] at h3
          simp [h, RealiseSpecEn] at h2
          simp [AbsState.restrict, <-h2, h3]

noncomputable def Verif.gnt_cnt (v : @Verif αi μ v r) (is : InfList αi) (n t : Nat) : Nat :=
match v.mem_gnt_fst_d ((v.sample is).get (v.spec_en_incl_start is n + t)), v.mem_gnt_snd_d ((v.sample is).get (v.spec_en_incl_start is n + t)) with
| false, false => 0
| true, false => 1
| true, true => 2
| false, true => 99999 -- unreachable

def Verif.outsMatchPref (v : @Verif αi μ v r) (is : InfList αi) (n t : Nat) : Prop :=
  ((v.cumm_outs_to is n t).map IbexOuts.interpret).flatten = (v.spec.outputs ((v.spec.seq is).get n) (is.get n)).take (v.gnt_cnt is n t)

theorem step_sample (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.ibex.step ((v.sample is).get n) = ((v.sample is).get (n + 1)).state := by
  simp [Verif.sample, InfList.map, InfList.zip, Ibex.seq, Ibex.run, InfList.inits, InfList.take_add_one]

theorem TopLevelMemoryBase (v : @Verif αi μ v r) (is : InfList αi) (n : Nat)
  (hf : v.mem_gnt_fst_q ((v.sample is).get (v.spec_en_incl_start is n)).state = false)
  (hs : v.mem_gnt_snd_q ((v.sample is).get (v.spec_en_incl_start is n)).state = false) :
  v.outsMatchPref is n 0 := by
  simp [Verif.outsMatchPref, Verif.cumm_outs_to, Verif.gnt_cnt, Verif.mem_gnt_fst_d, Verif.mem_gnt_snd_d, hf, hs, InfList.take, InfList.head, InfList.drop, IbexOuts.interpret, IbexOutsInsCopy]
  cases hg : ((v.sample is).get (v.spec_en_incl_start is n)).inputs.gnt_i
  . simp
  . have hr := GntImpliesReq v.ibex _ hg
    have hgf : v.mem_req_fst_d ((v.sample is).get (v.spec_en_incl_start is n)) := (by
        simp [Verif.mem_req_fst_d]
        exact And.intro hr hf)
    have hsoc : v.spec.routputs (v.abs ((v.sample is).get (v.spec_en_incl_start is n))) (v.absi ((v.sample is).get (v.spec_en_incl_start is n))) = (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) := by
        have hss := SpecStable _ _ n _ (And.intro (Nat.le_of_eq rfl) (start_before_end _ _)) hr
        rw [hss, Continuity, Realise _ _ n _ (And.intro (Nat.le_of_eq rfl) (start_before_end _ _)), Spec.outputs]
    cases hw : (v.ibex.outputs ((v.sample is).get (v.spec_en_incl_start is n))).data_we_o
    . simp
      have ⟨hsw, _⟩ := We _ ((v.sample is).get (v.spec_en_incl_start is n)) (SampledIsReachable _) hr
      simp [Verif.spec_mem_write, Verif.spec_mem_read, hw] at *
      match hso : v.spec_outs ((v.sample is).get (v.spec_en_incl_start is n)) with
      | [] => simp [hso] at *
      | .write _ _ _ :: _ => simp [hso] at hsw
      | .read a :: _ =>
        simp [Verif.spec_outs] at hso
        simp [<-hsoc, hso]
        have hsa := FstAddr _ _ (SampledIsReachable _) hgf
        simp [Verif.spec_mem_fst_addr, Verif.spec_outs, hso] at hsa
        exact hsa.symm
    . simp
      have ⟨hsw, _⟩ := We _ ((v.sample is).get (v.spec_en_incl_start is n)) (SampledIsReachable _) hr
      simp [Verif.spec_mem_write, hw] at hsw
      match hso : v.spec_outs ((v.sample is).get (v.spec_en_incl_start is n)) with
      | [] => simp [hso] at *
      | .read _ :: _ => simp [hso] at hsw
      | .write _ _ _ :: _ =>
        simp [Verif.spec_outs] at hso
        simp [<-hsoc, hso]
        have hsa := FstAddr _ _ (SampledIsReachable _) hgf
        simp [Verif.spec_mem_fst_addr, Verif.spec_outs, hso] at hsa
        simp [hsa]
        have hsd := FstWData _ _ (SampledIsReachable _) hgf hw
        simp [Verif.spec_mem_write_fst_wdata_mask, Verif.spec_outs, hso] at hsd
        simp [hsd]
        have hsd := FstBE _ _ (SampledIsReachable _) hgf hw
        simp [Verif.spec_mem_write_fst_be, Verif.spec_outs, hso] at hsd
        simp [hsd]

theorem end_next (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) : v.ibex.step ((v.sample is).get (v.spec_en_incl_end is n)) = ((v.sample is).get (v.spec_en_incl_start is (n + 1))).state := by
  simp [Verif.spec_en_incl_start, Verif.spec_en_incl_end, step_sample]

theorem SndGntImpliesFstGnt (v : @Verif αi μ va r) (is : InfList αi) (n : Nat) (h : v.mem_gnt_snd_d ((v.sample is).get n)) : v.mem_gnt_fst_d ((v.sample is).get n) := by
  match n with
  | 0 =>
    simp [Verif.mem_gnt_snd_d] at h
    have hr : ((v.sample is).get 0).state = v.ibex.init := by simp [Verif.sample, InfList.map, InfList.zip, Ibex.seq, Ibex.run, InfList.inits, InfList.take]
    simp [hr, MemGntFstInit v, MemGntSndInit v] at h
  | n + 1 =>
    simp [Verif.mem_gnt_fst_d]
    simp [Verif.mem_gnt_snd_d] at h
    exact h.by_cases
      (fun h =>
        have hq1 := MemGntSndQ v ((v.sample is).get n)
        have hq2 := MemGntFstQ v ((v.sample is).get n)
        match hs : v.spec_en ((v.sample is).get n) with
        | true => by
          simp [hs, step_sample] at *
          exact absurd h (Bool.eq_false_iff.mp hq1)
        | false => by
          simp [hs, step_sample] at *
          simp [hq2]
          simp [h] at hq1
          exact Or.intro_left _ (SndGntImpliesFstGnt v is n hq1)
      )
      (fun ⟨hg, hq⟩ => Or.intro_right _ hg)

theorem TopLevelMemoryPrefix (v : @Verif αi μ v r) (is : InfList αi) (n t : Nat) (ht : t ≤ v.spec_en_incl_end is n - v.spec_en_incl_start is n) :
  v.outsMatchPref is n t := by match n, t with
| 0, 0 =>
  exact TopLevelMemoryBase _ _ 0 (by
    simp [Verif.spec_en_incl_start, Verif.sample, InfList.map, Ibex.seq, InfList.zip, Ibex.run, InfList.inits, InfList.take]
    exact MemGntFstInit _) (by
    simp [Verif.spec_en_incl_start, Verif.sample, InfList.map, Ibex.seq, InfList.zip, Ibex.run, InfList.inits, InfList.take]
    exact MemGntSndInit _)
| n + 1, 0 =>
  have hfq := MemGntFstQ v ((v.sample is).get (v.spec_en_incl_end is n))
  have hsq := MemGntSndQ v ((v.sample is).get (v.spec_en_incl_end is n))
  rw [end_next] at hfq
  rw [end_next] at hsq
  have hse : v.spec_en ((v.sample is).get (v.spec_en_incl_end is n)) := by
    simp [Verif.spec_en_incl_end, Verif.kth_spec_en]
    have ⟨i, p⟩ := (v.sample is).kth_max_sep v.spec_en n (SpecEnLiveness v is)
    exact p
  simp [hse] at hfq
  simp [hse] at hsq
  exact TopLevelMemoryBase _ _ (n + 1) hfq hsq
| n, t + 1 =>
  let s := (v.sample is).get (v.spec_en_incl_start is n + t)
  have hs : (v.sample is).get (v.spec_en_incl_start is n + t) = s := rfl
  let s' := (v.sample is).get (v.spec_en_incl_start is n + t + 1)
  have hs' : (v.sample is).get (v.spec_en_incl_start is n + t + 1) = s' := rfl
  have prev := TopLevelMemoryPrefix v is n t (by linarith)
  rw [Verif.outsMatchPref] at prev
  rw [Verif.outsMatchPref, Verif.cumm_outs_to_split, List.map_append, List.map, List.flatten_append, prev]
  simp [IbexOuts.interpret, Verif.gnt_cnt]
  have hfq := MemGntFstQ v s
  have hsq := MemGntSndQ v s
  rw [step_sample, hs'] at hfq
  rw [step_sample, hs'] at hsq
  have nse : ¬v.spec_en s := match hn : n with
    | 0 => by
      have h : t < v.kth_spec_en is 0 := by
        simp [Verif.spec_en_incl_start, Verif.spec_en_incl_end] at ht
        exact Nat.lt_of_add_one_le ht
      simp [<-hs, Verif.spec_en_incl_start, InfList.kth_max_sep_not_first _ _ t _ h]
    | n + 1 => by
      have h1 : v.kth_spec_en is n < v.spec_en_incl_start is (n + 1) + t := by
        simp [Verif.spec_en_incl_start, Verif.spec_en_incl_end] at ht
        simp [Verif.spec_en_incl_start]
        linarith
      have h2 : v.spec_en_incl_start is (n + 1) + t < v.kth_spec_en is (n + 1) := by
        simp [Verif.spec_en_incl_start, Verif.spec_en_incl_end] at ht
        simp [Verif.spec_en_incl_start]
        have hlt : v.kth_spec_en is n < v.kth_spec_en is (n + 1) := InfList.kth_max_step_diff _ _ n (SpecEnLiveness v is)
        have ht' := Nat.add_le_add_left ht (v.kth_spec_en is n + 1)
        rw [Nat.add_sub_cancel' (Nat.add_one_le_of_lt hlt)] at ht'
        linarith
      have h := InfList.kth_max_sep_not_between _ _ n (v.spec_en_incl_start is (n + 1) + t) (SpecEnLiveness v is) (And.intro h1 h2)
      rw [hs] at h
      exact h
  simp [nse] at hfq
  simp [nse] at hsq
  simp [IbexOutsInsCopy]
  rw (occs := [2]) [Verif.mem_gnt_fst_d, Verif.mem_gnt_snd_d]
  rw [<-Nat.add_assoc, hfq, hsq, hs']
  have hle : v.spec_en_incl_start is n + t + 1 ≤ v.spec_en_incl_end is n := by
    rw [Nat.add_assoc, Nat.add_comm]
    have h := Nat.add_le_add_right ht (v.spec_en_incl_start is n)
    rw [Nat.sub_add_cancel (start_before_end _ _)] at h
    exact h
  cases hgf : v.mem_gnt_fst_d s
  . cases hb : v.mem_gnt_snd_d s
    . cases hg : s'.inputs.gnt_i
      . simp at *
      . have hr := GntImpliesReq v.ibex _ hg
        have hsoc : v.spec.routputs (v.abs s') (v.absi s') = (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) := by
          have hss := SpecStable _ _ n _ (And.intro (by linarith) hle) hr
          rw [hss, Continuity, Realise _ _ n _ (And.intro (by linarith) hle), Spec.outputs]
        simp [hgf] at hfq
        have ⟨hsw, hsr⟩ := We _ s' (SampledIsReachable _) hr
        have hsa := FstAddr v s' (SampledIsReachable _) (by simp [Verif.mem_req_fst_d, GntImpliesReq, hg, hfq])
        cases hw : (v.ibex.outputs s').data_we_o
        . simp [Verif.spec_mem_write, hw, Verif.spec_outs, hsoc] at hsw
          simp [Verif.spec_mem_read, hw, Verif.spec_outs, hsoc] at hsr
          match hso : (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) with
          | [] => simp [hso] at *
          | .write _ _ _ :: _ => simp [hso] at hsw
          | .read a :: _ =>
            simp [Verif.spec_mem_fst_addr, Verif.spec_outs, hsoc, hso] at hsa
            simp [List.take, hsa]
        . have ⟨hsw, hsr⟩ := We _ s' (SampledIsReachable _) hr
          simp [Verif.spec_mem_write, hw, Verif.spec_outs, hsoc] at hsw
          simp [Verif.spec_mem_read, hw, Verif.spec_outs, hsoc] at hsr
          match hso : (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) with
          | [] => simp [hso] at *
          | .read _ :: _ => simp [hso] at hsw
          | .write a d b :: _ =>
            simp [Verif.spec_mem_fst_addr, Verif.spec_outs, hsoc, hso] at hsa
            simp [List.take, hsa.symm]
            have hsd := FstWData v s' (SampledIsReachable _) (by simp [Verif.mem_req_fst_d, GntImpliesReq, hg, hfq]) hw
            simp [Verif.spec_mem_write_fst_wdata_mask, Verif.spec_outs, hsoc, hso] at hsd
            simp [hsd.symm]
            have hsd := FstBE v s' (SampledIsReachable _) (by simp [Verif.mem_req_fst_d, GntImpliesReq, hg, hfq]) hw
            simp [Verif.spec_mem_write_fst_be, Verif.spec_outs, hsoc, hso] at hsd
            simp [hsd.symm]
    . cases s'.inputs.gnt_i
      . simp at *
      . exact absurd (SndGntImpliesFstGnt _ _ _ hb) (Bool.eq_not.mp hgf)
  . cases hb : v.mem_gnt_snd_d s
    . cases hg : s'.inputs.gnt_i
      . simp at *
      . have hr := GntImpliesReq v.ibex _ hg
        have hsoc : v.spec.routputs (v.abs s') (v.absi s') = (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) := by
          have hss := SpecStable _ _ n _ (And.intro (by linarith) hle) hr
          rw [hss, Continuity, Realise _ _ n _ (And.intro (by linarith) hle), Spec.outputs]
        simp [hgf] at hfq
        have ⟨hsw, hsr⟩ := We _ s' (SampledIsReachable _) hr
        have hsa := SndAddr v s' (SampledIsReachable _) (by simp [Verif.mem_req_snd_d, GntImpliesReq, hg, hfq])
        cases hw : (v.ibex.outputs s').data_we_o
        . simp [Verif.spec_mem_write, hw, Verif.spec_outs, hsoc] at hsw
          simp [Verif.spec_mem_read, hw, Verif.spec_outs, hsoc] at hsr
          match hso : (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) with
          | [] => simp [hso] at *
          | .write _ _ _ :: _ => simp [hso] at *
          | .read _ :: .write _ _ _ :: _ =>
            have h := SpecOutTypes v.spec ((v.spec.seq is).get n) (is.get n)
            simp [hso] at h
          | [.read _] => simp [Verif.spec_mem_snd_addr, Verif.spec_outs, hsoc, hso] at hsa
          | .read _ :: .read a :: _ =>
            simp [Verif.spec_mem_snd_addr, Verif.spec_outs, hsoc, hso] at hsa
            simp [hsa]
        . simp at *
          simp [Verif.spec_mem_write, hw, Verif.spec_outs, hsoc] at hsw
          simp [Verif.spec_mem_read, hw, Verif.spec_outs, hsoc] at hsr
          match hso : (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) with
          | [] => simp [hso] at *
          | .read _ :: _ => simp [hso] at *
          | .write _ _ _ :: .read _ :: _ =>
            have h := SpecOutTypes v.spec ((v.spec.seq is).get n) (is.get n)
            simp [hso] at h
          | [.write _ _ _] => simp [Verif.spec_mem_snd_addr, Verif.spec_outs, hsoc, hso] at hsa
          | .write _ _ _ :: .write a d b :: _ =>
            simp [Verif.spec_mem_snd_addr, Verif.spec_outs, hsoc, hso] at hsa
            simp [hsa]
            have hsd := SndWData v s' (SampledIsReachable _) (by simp [Verif.mem_req_snd_d, GntImpliesReq, hg, hfq]) hw
            simp [Verif.spec_mem_write_snd_wdata_mask, Verif.spec_outs, hsoc, hso] at hsd
            simp [hsd.symm]
            have hsd := SndBE v s' (SampledIsReachable _) (by simp [Verif.mem_req_snd_d, GntImpliesReq, hg, hfq]) hw
            simp [Verif.spec_mem_write_snd_be, Verif.spec_outs, hsoc, hso] at hsd
            simp [hsd.symm]
    . cases hc : s'.inputs.gnt_i
      . simp at *
      . have h := step_sample v is (v.spec_en_incl_start is n + t)
        simp [hs, hs'] at *
        have h2 : v.mem_gnt_snd_q s'.state := by
          simp [<-h, MemGntSndQ, nse]
          exact hb
        exact absurd (GntImpliesReq v.ibex _ hc) (LSUMaxTwoReqs _ _ (SampledIsReachable _) h2)

theorem sample_spec_en_end (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) : (v.sample is).get (v.spec_en_incl_end is n) = (v.sample_en is).get n := by
  simp [Verif.spec_en_incl_end, Verif.sample_en]

theorem cancel_spec_en (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.spec_en_incl_start is n + (v.spec_en_incl_end is n - v.spec_en_incl_start is n) = v.spec_en_incl_end is n :=
  Nat.add_sub_cancel' (start_before_end _ _)

theorem TopLevelMemory (v : @Verif αi μ v r) (is : InfList αi) (n : Nat) :
  v.check (v.spec.outputs ((v.spec.seq is).get n) (is.get n)) (v.cumm_outs is n) := by
  rw [Verif.check]
  have h := TopLevelMemoryPrefix v is n ((v.spec_en_incl_end is n) - (v.spec_en_incl_start is n)) (by simp)
  rw [Verif.outsMatchPref] at h
  let s := (v.sample is).get (v.spec_en_incl_start is n + (v.spec_en_incl_end is n - v.spec_en_incl_start is n))
  have hs : (v.sample is).get (v.spec_en_incl_start is n + (v.spec_en_incl_end is n - v.spec_en_incl_start is n)) = s := rfl
  have hse : v.spec_en s = true := by
    rw [<-hs, cancel_spec_en, sample_spec_en_end _ _ _, SampleEnIsSpecEn]
  have h3 : (v.spec.outputs ((v.spec.seq is).get n) (is.get n)).length = (v.gnt_cnt is n ((v.spec_en_incl_end is n) - (v.spec_en_incl_start is n))) := by
    rw [Verif.gnt_cnt]
    cases ha : v.mem_gnt_fst_d s
    . cases hb : v.mem_gnt_snd_d s
      . simp
        have h4 := mt (FstEnd _ _ (SampledIsReachable _) hse) (Bool.eq_false_iff.mp ha)
        simp [Verif.spec_mem_en, Verif.spec_outs, cancel_spec_en] at h4
        rw [Realise _ _ n (v.spec_en_incl_end is n) (And.intro (start_before_end _ _) (by simp)), sample_spec_en_end] at h4
        simp [Continuity] at h4
        exact h4
      . simp
        have h2 := SndGntImpliesFstGnt _ _ _ hb
        exact absurd h2 (Bool.eq_false_iff.mp ha)
    . cases hb : v.mem_gnt_snd_d s
      . simp
        have h5 : v.spec_mem_en s := MemEnG _ _ (SampledIsReachable _) ha
        simp [<-hs, Verif.spec_mem_en, Verif.spec_outs, cancel_spec_en] at h5
        rw [Realise _ _ n (v.spec_en_incl_end is n) (And.intro (start_before_end _ _) (by simp)), sample_spec_en_end] at h5
        simp [Continuity] at h5
        rw [<-List.length_eq_zero_iff] at h5
        have h5 := Nat.zero_lt_of_ne_zero h5
        have h6 := mt (SndEnd _ _ (SampledIsReachable _) hse) (Bool.eq_false_iff.mp hb)
        simp [Verif.spec_mem_en_snd, Verif.spec_outs, cancel_spec_en] at h6
        rw [Realise _ _ n (v.spec_en_incl_end is n) (And.intro (start_before_end _ _) (by simp)), sample_spec_en_end] at h6
        simp [Continuity] at h6
        simp [Spec.outputs]
        linarith [h5, h6]
      . simp
        have h6 : v.spec_mem_en_snd s := SndEnG _ _ (SampledIsReachable _) hb
        simp [<-hs, Verif.spec_mem_en_snd, Verif.spec_outs, cancel_spec_en] at h6
        rw [Realise _ _ n (v.spec_en_incl_end is n) (And.intro (start_before_end _ _) (by simp)), sample_spec_en_end] at h6
        simp [Continuity] at h6
        have h5 := SpecOutLimit v.spec ((v.spec.seq is).get n) (is.get n)
        simp [Spec.outputs] at h5
        simp [Spec.outputs]
        linarith [h5, h6]
  have h2 := (List.take_eq_self_iff (v.spec.outputs ((v.spec.seq is).get n) (is.get n))).mpr (Nat.le_of_eq h3)
  rw [h2] at h
  rw [Verif.cumm_outs]
  exact h.symm

theorem sum_diffs_nat (f : Nat -> Nat) (hf : ∀ (n : Nat), f n ≤ f n.succ) :
  let l : InfList Nat := { get := fun n => f n.succ - f n }
  ∀ (i j : Nat), ((l.drop j).take i).val.sum = f (i + j) - f j
  := fun i j => match i, j with
      | 0, _ => by simp [InfList.take]
      | .succ i, j => by
        have h := sum_diffs_nat f hf i j.succ
        simp [InfList.take, InfList.tail_as_drop]
        rw [h]
        simp [InfList.drop, InfList.head]
        calc f (j + 1) - f j + (f (i + (j + 1)) - f (j + 1))
          _ = (f (i + (j + 1)) - f (j + 1)) + (f (j + 1) - f j) := by ring_nf
          _ = f (i + (j + 1)) - f (j + 1) + f (j + 1) - f j := by rw [Nat.add_sub_assoc (hf j) _]
          _ = f (i + (j + 1)) - f j := by rw [Nat.sub_add_cancel (monotone f hf (by linarith))]
          _ = f (i + (1 + j)) - f j := by simp [Nat.add_comm]
          _ = f (i + 1 + j) - f j := by simp [Nat.add_assoc]

theorem sum_diffs_full_nat (f : Nat -> Nat) (hf : ∀ (n : Nat), f n ≤ f n.succ) :
  let l : InfList Nat := { get := fun n => f n.succ - f n }
  ∀ (i : Nat), (l.take i).val.sum = f i - f 0
  := fun i => by
    have h := sum_diffs_nat f hf i 0
    simp [InfList.drop] at h
    exact h

theorem ObservationalCorrectness' (v : @Verif αi μ v r) (is : InfList αi) :
  let spec_outs := (v.sample_spec is).map fun (s, i) => v.spec.outputs s i
  let ibex_outs := (v.sample is).map fun s => (v.ibex.outputs s).interpret
  ∃ (ln : InfList Nat), (spec_outs.zip (ibex_outs.chunk ln).val).map_all fun (x, y) => x = y.flatten
  -- FIXME: Flatten this somehow? Would make for a nicer final statement.
:=
  let ln := {
    get := fun n =>
      match n with
      | 0 => (v.kth_spec_en is 0).succ
      | .succ n =>
        let i := v.kth_spec_en is n
        let j := v.kth_spec_en is n.succ
        j - i
  }

  have hln := by
    simp [InfList.map_all, InfList.zip, InfList.chunk]
    intro n
    let i := v.kth_spec_en is n
    let j := v.kth_spec_en is n.succ
    have h := TopLevelMemory v is n
    match n with
    | 0 =>
      simp [ln, InfList.take, InfList.drop, InfList.head, InfList.map, Verif.sample_spec, InfList.zip]
      simp [Verif.cumm_outs, Verif.cumm_outs_to, InfList.take_map_assoc, Verif.spec_en_incl_start, Verif.check] at h
      exact h
    | .succ n =>
      simp [ln, InfList.take, InfList.drop, InfList.head, InfList.map, Verif.sample_spec, InfList.zip]
      simp [Verif.cumm_outs, Verif.cumm_outs_to, InfList.take_map_assoc, Verif.spec_en_incl_start, Verif.spec_en_incl_end, Verif.check] at h
      have h2 :
        InfList.map (fun s => (v.ibex.outputs s).interpret) (InfList.drop (v.kth_spec_en is n + 1) (v.sample is)) =
        { get := fun x => (v.ibex.outputs ((v.sample is).get (v.kth_spec_en is 0 + 1 + (InfList.take n ln.tail).val.sum + x))).interpret }
      := by
        simp [InfList.map]
        funext x
        simp [InfList.drop]
        unfold ln
        have h : ∀ (n : Nat), v.kth_spec_en is n ≤ v.kth_spec_en is n.succ :=
          fun (n : Nat) => Nat.le_of_lt (InfList.kth_max_step_diff_many _ _ _ _ (by simp) _)
        rw [InfList.tail, sum_diffs_full_nat _ h]
        rw [<-Nat.add_sub_assoc]
        . simp [Nat.add_comm, Nat.add_sub_assoc]
        . match n with
          | 0 => exact Nat.le_of_eq rfl
          | .succ n => exact Nat.le_of_lt (InfList.kth_max_step_diff_many _ _ _ _ (by simp) _)
      rw [<-h2]
      have hn : 1 ≤ v.kth_spec_en is (n + 1) - v.kth_spec_en is n := Nat.sub_pos_of_lt (InfList.kth_max_step_diff _ _ _ _)
      rw [<-Nat.sub_sub, Nat.sub_add_cancel hn] at h
      exact h
  ⟨ln, hln⟩
