import Mathlib.Tactic

theorem monotone (f : Nat -> Nat) (hf : ∀ (n : Nat), f n ≤ f (n + 1)) :
  a ≤ b -> f a ≤ f b :=
  fun h =>
  if he : a < b then
    Nat.le_trans (hf a) (monotone f hf (Nat.add_one_le_of_lt he))
  else by
    rw [Nat.not_lt_eq _ _] at he
    rw [Nat.eq_iff_le_and_ge.mpr (And.intro he h)]

structure InfList (α : Type u) where
  get : Nat -> α

def InfList.head (l : InfList α) : α := l.get 0
def InfList.tail (l : InfList α) : InfList α := { get := fun x => l.get x.succ }
def InfList.cons (x : α) (l : InfList α) : InfList α := { get := fun n => match n with | 0 => x | .succ n => l.get n }

def InfList.zip (l1 : InfList α) (l2 : InfList β) : InfList (α × β) := { get := fun x => (l1.get x, l2.get x) }

def InfList.map (f : α -> β) (l : InfList α) : InfList β := { get := fun n => f (l.get n) }

def InfList.take (n : Nat) (l : InfList α) : { l : List α // l.length = n} := match n with
| 0 => ⟨[], rfl⟩
| .succ n =>
  have ⟨x, xs⟩ := l.tail.take n
  ⟨l.head :: x, by rw [List.length_cons, xs]⟩
def InfList.drop (n : Nat) (l : InfList α) : InfList α := { get := fun x => l.get (n + x) }

theorem InfList.take_add_one { l : InfList α } : l.take (n + 1) = (l.take n).val ++ [l.get n] := match n with
| 0 => by simp [InfList.take, InfList.head]
| n + 1 => by
  rw [InfList.take]
  simp
  rw [@InfList.take_add_one _ n l.tail, <-List.cons_append, InfList.take]
  simp [InfList.tail]

@[simp]
theorem InfList.drop_0_eq (l : InfList α) : l.drop 0 = l := by simp [drop]
@[simp]
theorem InfList.drop_assoc_eq (l : InfList α) : .drop a (l.drop b) = l.drop (b + a) := by simp [drop, <-Nat.add_assoc]

def InfList.inits (l : InfList α) : InfList (List α) := { get := fun n => l.take n }

def InfList.any_within : Nat -> (f : α -> Prop) -> InfList α -> Prop
| 0, _, _ => False
| .succ n, f, l => f l.head ∨ l.tail.any_within n f

def InfList.nextIndex (f : α -> Bool) (l : InfList α) (hn : l.any_within n fun x => f x) : { i : Nat // f (l.get i) ∧ ∀ (k: Nat), k < i -> ¬f (l.get k) } :=
  if h : f l.head then ⟨0, ⟨h, by simp⟩⟩
  else match n with
    | 0 => hn.elim
    | .succ n =>
      have ⟨i, ⟨p1, p2⟩⟩ := @l.tail.nextIndex α n f (by
        simp [InfList.any_within, h] at hn
        simp [*]
      )
      have p2' : ∀ (k : Nat), k < i.succ -> ¬f (l.get k) := fun k hk =>
        match k with
        | 0 => h
        | k + 1 => p2 k (Nat.lt_of_add_lt_add_right hk)
      ⟨i.succ, ⟨p1, p2'⟩⟩

def InfList.next (f : α -> Bool) (l : InfList α) (hn : l.any_within n fun x => f x) : α := l.get (l.nextIndex f hn)

-- def InfList.kth_max_sep (f : α -> Bool) (l : InfList α) (k : Nat) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) : { i : Nat // f (l.get i) } :=
  -- have ⟨i, p⟩ := @InfList.nextIndex α n f l (by
  --   have h := hn 0
  --   rw [InfList.drop_0_eq] at h
  --   exact h
  -- )
--   match k with
--   | 0 => ⟨i, p.left⟩
--   | .succ k =>
--     have ⟨i2, p⟩ := @InfList.kth_max_sep _ n f (l.drop i.succ) k (fun s => by simp [*] at *)
--     ⟨i.succ + i2, p⟩

def InfList.kth_max_sep (f : α -> Bool) (l : InfList α) (k : Nat) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) : { i : Nat // f (l.get i) } :=
  match k with
  | 0 =>
    have ⟨i, p⟩ := @InfList.nextIndex α n f l (by
      have h := hn 0
      rw [InfList.drop_0_eq] at h
      exact h
    )
    ⟨i, p.left⟩
  | .succ k =>
    have ⟨i2, _⟩ := @InfList.kth_max_sep _ n f l k (fun s => by simp [*] at *)
    have ⟨i, p⟩ := @InfList.nextIndex α n f (l.drop (i2 + 1)) (hn (i2 + 1))
    ⟨i2 + 1 + i, p.left⟩

theorem InfList.kth_max_step_diff (f : α -> Bool) (l : InfList α) (k : Nat) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) :
  InfList.kth_max_sep f l k hn < (InfList.kth_max_sep f l (k + 1) hn).val := by
match k with
| 0 =>
  simp [InfList.kth_max_sep]
  linarith
| k + 1 =>
  simp [InfList.kth_max_sep]
  linarith


theorem InfList.kth_max_step_diff_many (f : α -> Bool) (l : InfList α) (k k2 : Nat) (hk : k < k2) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) :
  InfList.kth_max_sep f l k hn < (InfList.kth_max_sep f l k2 hn).val := by
  if h : k + 1 < k2 then
    have h2 := InfList.kth_max_step_diff_many f l (k + 1) k2 h hn
    have h3 := InfList.kth_max_step_diff f l k hn
    exact Nat.lt_trans h3 h2
  else
    have h3 : k2 = k + 1 := by linarith
    rw [h3]
    exact InfList.kth_max_step_diff f l k hn

theorem InfList.kth_max_sep_not_first (f : α -> Bool) (l : InfList α) (t : Nat) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) (hk : t < l.kth_max_sep f 0 hn) :
  ¬f (l.get t) := by
  simp [kth_max_sep] at hk
  let r := @InfList.nextIndex α n f l (by
    have h := hn 0
    rw [InfList.drop_0_eq] at h
    exact h
  )
  have h : r = @InfList.nextIndex α n f l (by
    have h := hn 0
    rw [InfList.drop_0_eq] at h
    exact h
  ) := by rfl
  let ⟨i, p⟩ := r
  simp [<-h] at hk
  exact p.right t hk

theorem InfList.kth_max_sep_not_between (f : α -> Bool) (l : InfList α) (k t : Nat) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) (hk : l.kth_max_sep f k hn < t ∧ t < l.kth_max_sep f (k + 1) hn) :
  ¬f (l.get t) := by
  let i2 := @InfList.kth_max_sep _ n f l k (fun s => by simp [*] at *)
  have i2h : i2 = @InfList.kth_max_sep _ n f l k (fun s => by simp [*] at *) := rfl
  let ip := @InfList.nextIndex α n f (l.drop (i2 + 1)) (hn (i2 + 1))
  let r : { i : Nat // f (l.get i) } := ⟨i2 + 1 + ip.val, ip.property.left⟩
  have hr1 : r = l.kth_max_sep f (k + 1) hn := rfl
  have hr2 : r.val = i2 + 1 + ip.val := rfl
  rw [<-hr1, hr2] at hk
  have ⟨i, ⟨pa, pb⟩⟩ := ip
  simp [drop] at pb
  have ⟨ri, _⟩ := r
  simp at hk
  have ⟨i2i, _⟩ := i2
  simp at pb
  simp [<-i2h] at *
  let k := t - (i2i + 1)
  have bh := pb k (by
    have ⟨a, b⟩ := hk
    rw [Nat.add_comm] at b
    rw [Nat.sub_lt_iff_lt_add hk.left]
    exact b
  )
  rw [Nat.add_sub_cancel' hk.left] at bh
  exact bh

def InfList.filter_max_sep (f : α -> Bool) (l : InfList α) (hn : ∀ (s : Nat), (l.drop s).any_within n fun x => f x) : InfList { x : α // f x } :=
  {
    get := fun x =>
      have ⟨i, p⟩ := l.kth_max_sep f x hn
      ⟨l.get i, p⟩
  }

def InfList.map_all (f : α -> Prop) (l : InfList α) : Prop := ∀ (n : Nat), f (l.get n)

def InfList.chunk (l1 : InfList α) (ln : InfList Nat) : { lr : InfList (List α) // (lr.zip ln).map_all fun (a, n) => a.length = n } :=
  let xs := { get := fun n => (l1.drop ((ln.take n).val.sum)).take (ln.get n) }
  ⟨xs, fun n => by
    let l := take (ln.get n) (drop (take n ln).val.sum l1)
    exact l.property⟩

theorem InfList.take_map_assoc (f : α -> β) (l : InfList α) :
  (n : Nat) -> (l.take n).val.map f = ((l.map f).take n).val
| 0 => by simp [InfList.take]
| .succ n => by
  simp [InfList.take]
  rw [InfList.take_map_assoc]
  constructor
  simp [InfList.map, InfList.head]
  simp [InfList.map, InfList.tail]

theorem InfList.tail_as_drop (l : InfList α) : l.tail = l.drop 1 := by simp [InfList.tail, InfList.drop, Nat.add_comm]

-- def InfList.flatten_take (l : InfList (List α)) (n : Nat) : List α

def InfList.flattened_eq_len (l1 l2 : InfList (List α)) : Prop :=
  ∀ (n : Nat),
    (∃ (k : Nat), n < (l1.take k).val.flatten.length) <-> (∃ (k : Nat), n < (l2.take k).val.flatten.length)

def InfList.flattened_eq (l1 l2 : InfList (List α)) : Prop :=
  flattened_eq_len l1 l2 ∧
  ∀ (n k : Nat),
    n < (l1.take k).val.flatten.length -> (l1.take k).val.flatten.take n = (l2.take k).val.flatten.take n

-- theorem InfList.chunk_eq_to_flattened_eq (l1 l2 : InfList (List α))
--   (hc : ∃ (ln : InfList Nat), (l1.zip (l2.chunk ln).val).map_all fun (x, y) => x = y.flatten)
-- : l1.flattened_eq_len l2
--   := fun n => by
--     have ⟨ln, hln⟩ := hc
--     constructor
--     . intro ⟨k, hk⟩
--       refine ⟨(ln.take k).val.sum, ?_⟩
--       sorry
--     . intro ⟨k, hk⟩
--       sorry
  -- have ⟨ln, hc⟩ := hc
  -- simp [map_all, zip] at hc

  -- constructor
  -- . intro hx
  --   constructor
  --   . sorry
  --   . match k1, k2 with
  --     | k1 + 1, k2 + 1 =>
  --       have ⟨ihl, ihr⟩ := chunk_eq_to_flattened_eq l1 l2 ⟨ln, sorry⟩ n k1 k2
  --       have ⟨ihll, ihlr⟩ := ihl sorry
  --       -- simp [flattened_eq] at hc
  --       simp [take_add_one]
  --       rw [hc, List.take_append, List.take_append, ihlr]
  --       simp
  --       rw [<-hc]
  --       sorry
  --     | _, 0 => sorry
  -- . intro hy
  --   constructor
  --   sorry
  --   sorry
  -- match n, hk1 : k1, hk2 : k2, hx : ((take k1 l1).val).flatten, hy : ((take k2 l2).val).flatten with
  -- | 0, _, _, _, _ => rfl
  -- | n + 1, k1 + 1, k2 + 1, x :: xs, y :: ys =>
  --   rw [List.take.eq_def, List.take.eq_def]
  --   simp
  --   have h := hc 0
  --   -- rw [hk1, List.take] at hx
  --   simp [chunk, drop, take, List.flatten] at h
  --   -- constructor h : ((take k1 l1).val).flatten
  --   -- rw [List.flatten] at hx
  --   sorry
  -- | n + 1, _, _, _, _ => sorry
