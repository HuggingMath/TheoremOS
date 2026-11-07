import Mathlib

/-!
# Edit distance and longest common subsequences

Unit-cost edit distance on lists. Contents: length-indexed chains `StepChain R n x y` of a step
relation (concatenation, reversal for symmetric steps, monotone images, Lipschitz potentials);
single edits `IsEditStep` (insertion, deletion, substitution at any position) with their
constructors, symmetry, context closure and length bound; `editDist x y`, the least number of
edits, as a metric on `List α` (`editDist_self`, `editDist_eq_zero_iff`, `editDist_comm`,
`editDist_triangle`); `|x| ≤ |y| + ed`, `ed ≤ |x| + |y|`, `ed ≤ max |x| |y|`, the Hamming bound for
equal lengths, prefix/suffix and concatenation bounds; `lcsLength x y`, the longest common
subsequence, with `max |x| |y| ≤ lcs + ed` and `ed + 2 lcs ≤ |x| + |y|`; and the block-code bounds
`ed (map f x) (map f y) ≤ ed x y` and `ed (flatMap c x) (flatMap c y) ≤ w · ed x y` when every
codeword has length `w`.

Sources: V. I. Levenshtein, Binary codes capable of correcting deletions, insertions, and
reversals, Soviet Physics Doklady 10 (1966) 707–710; R. A. Wagner and M. J. Fischer, The
string-to-string correction problem, J. ACM 21 (1974) 168–173; D. Gusfield, *Algorithms on Strings,
Trees, and Sequences*, Cambridge University Press, 1997, Sections 11.1–11.3 and 11.6. Textbook
material; nothing here is specific to a benchmark problem.

Bridges: a statement with its own inductive single edit (`insert`/`delete`/`substitute` written as
`p ++ q ↦ p ++ a :: q`, `p ++ a :: q ↦ p ++ q`, `p ++ a :: q ↦ p ++ b :: q`) and its own script
inductive gets `Script x y n ↔ StepChain IsEditStep n x y` by induction in each direction, using
`IsEditStep.insert`/`delete`/`substitute` one way and `rcases` on `IsEditStep` the other way; then
`sInf {n | Script x y n} = editDist x y` by `sInf_eq_editDist`. A longest common subsequence
defined as `sSup {n | ∃ z, z <+ x ∧ z <+ y ∧ z.length = n}` is `lcsLength x y` by `rfl`.
-/

namespace TheoremOS.Combinatorics

open List

universe u v

section StepChain

variable {β : Type u}

/-- `StepChain R n x y`: `y` is reached from `x` by exactly `n` steps of `R`. -/
inductive StepChain (R : β → β → Prop) : ℕ → β → β → Prop
  | nil (x : β) : StepChain R 0 x x
  | cons {n : ℕ} {x y z : β} : R x y → StepChain R n y z → StepChain R (n + 1) x z

variable {R : β → β → Prop}

theorem StepChain.of_eq {m n : ℕ} {x y : β} (h : StepChain R m x y) (hmn : m = n) :
    StepChain R n x y := hmn ▸ h

theorem StepChain.single {x y : β} (h : R x y) : StepChain R 1 x y := .cons h (.nil y)

theorem StepChain.eq_of_zero {x y : β} (h : StepChain R 0 x y) : x = y := by
  cases h
  rfl

theorem StepChain.trans {m n : ℕ} {x y z : β} (h₁ : StepChain R m x y)
    (h₂ : StepChain R n y z) : StepChain R (m + n) x z := by
  induction h₁ with
  | nil x => exact h₂.of_eq (Nat.zero_add n).symm
  | cons hxy _ ih => exact (StepChain.cons hxy (ih h₂)).of_eq (by omega)

/-- Reversal of a chain of a symmetric relation. -/
theorem StepChain.symm (hR : ∀ a b, R a b → R b a) {n : ℕ} {x y : β}
    (h : StepChain R n x y) : StepChain R n y x := by
  induction h with
  | nil x => exact .nil x
  | cons hxy _ ih => exact ih.trans (.single (hR _ _ hxy))

/-- Image of a chain under a map sending `R`-steps to `R'`-steps. -/
theorem StepChain.map {γ : Type v} {R' : γ → γ → Prop} (g : β → γ)
    (hg : ∀ a b, R a b → R' (g a) (g b)) {n : ℕ} {x y : β} (h : StepChain R n x y) :
    StepChain R' n (g x) (g y) := by
  induction h with
  | nil x => exact .nil _
  | cons hxy _ ih => exact .cons (hg _ _ hxy) ih

theorem StepChain.mono {R' : β → β → Prop} (hR : ∀ a b, R a b → R' a b) {n : ℕ} {x y : β}
    (h : StepChain R n x y) : StepChain R' n x y :=
  h.map id hR

/-- A potential that grows by at most one per step grows by at most `n` along `n` steps. -/
theorem StepChain.le_add (φ : β → ℕ) (hφ : ∀ a b, R a b → φ b ≤ φ a + 1) {n : ℕ} {x y : β}
    (h : StepChain R n x y) : φ y ≤ φ x + n := by
  induction h with
  | nil x => exact Nat.le_add_right _ _
  | cons hxy _ ih => have := hφ _ _ hxy; omega

/-- Real-valued form: a potential with increments at most `c` grows by at most `n c`. -/
theorem StepChain.le_add_mul (φ : β → ℝ) (c : ℝ) (hφ : ∀ a b, R a b → φ b ≤ φ a + c) {n : ℕ}
    {x y : β} (h : StepChain R n x y) : φ y ≤ φ x + n * c := by
  induction h with
  | nil x => simp
  | cons hxy _ ih =>
    have := hφ _ _ hxy
    push_cast
    linarith

end StepChain

section EditStep

variable {α : Type u}

/-- One unit-cost edit: an insertion, a deletion or a substitution, at any position. -/
def IsEditStep (u v : List α) : Prop :=
  (∃ p q : List α, ∃ a : α, u = p ++ q ∧ v = p ++ a :: q) ∨
  (∃ p q : List α, ∃ a : α, u = p ++ a :: q ∧ v = p ++ q) ∨
  (∃ p q : List α, ∃ a b : α, u = p ++ a :: q ∧ v = p ++ b :: q)

namespace IsEditStep

theorem insert (p q : List α) (a : α) : IsEditStep (p ++ q) (p ++ a :: q) :=
  Or.inl ⟨p, q, a, rfl, rfl⟩

theorem delete (p q : List α) (a : α) : IsEditStep (p ++ a :: q) (p ++ q) :=
  Or.inr (Or.inl ⟨p, q, a, rfl, rfl⟩)

theorem substitute (p q : List α) (a b : α) : IsEditStep (p ++ a :: q) (p ++ b :: q) :=
  Or.inr (Or.inr ⟨p, q, a, b, rfl, rfl⟩)

theorem symm {u v : List α} (h : IsEditStep u v) : IsEditStep v u := by
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · exact delete p q a
  · exact insert p q a
  · exact substitute p q b a

theorem insert_head (a : α) (x : List α) : IsEditStep x (a :: x) := insert [] x a

theorem delete_head (a : α) (x : List α) : IsEditStep (a :: x) x := delete [] x a

theorem substitute_head (a b : α) (x : List α) : IsEditStep (a :: x) (b :: x) :=
  substitute [] x a b

theorem append_left (w : List α) {u v : List α} (h : IsEditStep u v) :
    IsEditStep (w ++ u) (w ++ v) := by
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · simpa using insert (w ++ p) q a
  · simpa using delete (w ++ p) q a
  · simpa using substitute (w ++ p) q a b

theorem append_right (w : List α) {u v : List α} (h : IsEditStep u v) :
    IsEditStep (u ++ w) (v ++ w) := by
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · simpa using insert p (q ++ w) a
  · simpa using delete p (q ++ w) a
  · simpa using substitute p (q ++ w) a b

theorem cons (c : α) {u v : List α} (h : IsEditStep u v) : IsEditStep (c :: u) (c :: v) :=
  append_left [c] h

theorem length_le {u v : List α} (h : IsEditStep u v) : v.length ≤ u.length + 1 := by
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩ <;>
    simp <;> omega

theorem map {γ : Type v} (f : α → γ) {u v : List α} (h : IsEditStep u v) :
    IsEditStep (u.map f) (v.map f) := by
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · simpa using insert (p.map f) (q.map f) (f a)
  · simpa using delete (p.map f) (q.map f) (f a)
  · simpa using substitute (p.map f) (q.map f) (f a) (f b)

end IsEditStep

/-- Unit-cost edit distance: the least length of an edit chain from `x` to `y`. -/
noncomputable def editDist (x y : List α) : ℕ := sInf {n | StepChain IsEditStep n x y}

/-- Deleting every letter of `x` takes `|x|` steps. -/
theorem stepChain_length_nil (x : List α) : StepChain IsEditStep x.length x [] := by
  induction x with
  | nil => exact .nil _
  | cons a x ih => exact (StepChain.cons (IsEditStep.delete_head a x) ih).of_eq (by simp)

/-- Delete all of `x`, then insert all of `y`. -/
theorem stepChain_length_add (x y : List α) :
    StepChain IsEditStep (x.length + y.length) x y :=
  (stepChain_length_nil x).trans ((stepChain_length_nil y).symm fun _ _ h => h.symm)

theorem editDist_le {n : ℕ} {x y : List α} (h : StepChain IsEditStep n x y) :
    editDist x y ≤ n :=
  Nat.sInf_le h

/-- The infimum is attained. -/
theorem stepChain_editDist (x y : List α) : StepChain IsEditStep (editDist x y) x y :=
  Nat.sInf_mem (s := {n | StepChain IsEditStep n x y}) ⟨_, stepChain_length_add x y⟩

/-- Bridge: any predicate equivalent to the chain predicate has the same infimum. -/
theorem sInf_eq_editDist {P : ℕ → Prop} {x y : List α}
    (hP : ∀ n, P n ↔ StepChain IsEditStep n x y) : sInf {n | P n} = editDist x y := by
  unfold editDist
  congr 1
  ext n
  exact hP n

theorem editDist_le_length_add (x y : List α) : editDist x y ≤ x.length + y.length :=
  editDist_le (stepChain_length_add x y)

@[simp] theorem editDist_self (x : List α) : editDist x x = 0 :=
  Nat.eq_zero_of_le_zero (editDist_le (.nil x))

theorem editDist_eq_zero_iff {x y : List α} : editDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have := stepChain_editDist x y
    rw [h] at this
    exact this.eq_of_zero
  · rintro rfl
    exact editDist_self x

theorem editDist_pos {x y : List α} (h : x ≠ y) : 0 < editDist x y :=
  Nat.pos_of_ne_zero (mt editDist_eq_zero_iff.mp h)

theorem editDist_comm (x y : List α) : editDist x y = editDist y x :=
  le_antisymm (editDist_le ((stepChain_editDist y x).symm fun _ _ h => h.symm))
    (editDist_le ((stepChain_editDist x y).symm fun _ _ h => h.symm))

theorem editDist_triangle (x y z : List α) : editDist x z ≤ editDist x y + editDist y z :=
  editDist_le ((stepChain_editDist x y).trans (stepChain_editDist y z))

theorem IsEditStep.editDist_le_one {u v : List α} (h : IsEditStep u v) : editDist u v ≤ 1 :=
  editDist_le (.single h)

/-- Lengths are `1`-Lipschitz for the edit distance. -/
theorem length_le_length_add_editDist (x y : List α) : y.length ≤ x.length + editDist x y :=
  (stepChain_editDist x y).le_add List.length fun _ _ h => h.length_le

theorem length_sub_length_le_editDist (x y : List α) : y.length - x.length ≤ editDist x y := by
  have := length_le_length_add_editDist x y
  omega

theorem editDist_append_left (w x y : List α) : editDist (w ++ x) (w ++ y) ≤ editDist x y :=
  editDist_le ((stepChain_editDist x y).map (w ++ ·) fun _ _ h => h.append_left w)

theorem editDist_append_right (w x y : List α) : editDist (x ++ w) (y ++ w) ≤ editDist x y :=
  editDist_le ((stepChain_editDist x y).map (· ++ w) fun _ _ h => h.append_right w)

theorem editDist_cons_cons_self (a : α) (x y : List α) :
    editDist (a :: x) (a :: y) ≤ editDist x y :=
  editDist_append_left [a] x y

/-- Concatenation is subadditive. -/
theorem editDist_append_le (x₁ x₂ y₁ y₂ : List α) :
    editDist (x₁ ++ x₂) (y₁ ++ y₂) ≤ editDist x₁ y₁ + editDist x₂ y₂ :=
  (editDist_triangle _ (y₁ ++ x₂) _).trans
    (add_le_add (editDist_append_right x₂ x₁ y₁) (editDist_append_left y₁ x₂ y₂))

theorem editDist_cons_cons_le (a b : α) (x y : List α) :
    editDist (a :: x) (b :: y) ≤ editDist x y + 1 :=
  (editDist_triangle _ (b :: x) _).trans (by
    have := (IsEditStep.substitute_head a b x).editDist_le_one
    have := editDist_cons_cons_self b x y
    omega)

theorem editDist_cons_left_le (a : α) (x y : List α) :
    editDist (a :: x) y ≤ editDist x y + 1 :=
  (editDist_triangle _ x _).trans (by
    have := (IsEditStep.delete_head a x).editDist_le_one
    omega)

theorem editDist_cons_right_le (a : α) (x y : List α) :
    editDist x (a :: y) ≤ editDist x y + 1 := by
  rw [editDist_comm, editDist_comm x y]
  exact editDist_cons_left_le a y x

@[simp] theorem editDist_nil_left (y : List α) : editDist [] y = y.length :=
  le_antisymm (by simpa using editDist_le_length_add [] y)
    (by simpa using length_le_length_add_editDist [] y)

@[simp] theorem editDist_nil_right (x : List α) : editDist x [] = x.length := by
  rw [editDist_comm, editDist_nil_left]

/-- Substitute along the shorter word, then insert or delete the rest. -/
theorem editDist_le_max_length : ∀ x y : List α, editDist x y ≤ max x.length y.length
  | [], y => by simp
  | x, [] => by simp
  | a :: x, b :: y => by
    have h := editDist_le_max_length x y
    have h' := editDist_cons_cons_le a b x y
    simp only [List.length_cons]
    omega

/-- For equal lengths the edit distance is at most the number of mismatched positions. -/
theorem editDist_le_countP_zip [DecidableEq α] :
    ∀ x y : List α, x.length = y.length →
      editDist x y ≤ (x.zip y).countP (fun p => p.1 ≠ p.2)
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: x, b :: y, h => by
    have ih := editDist_le_countP_zip x y (by simpa using h)
    have hab : editDist (a :: x) (b :: y) ≤ editDist x y + (if a = b then 0 else 1) := by
      split_ifs with hab
      · subst hab
        simpa using editDist_cons_cons_self a x y
      · exact editDist_cons_cons_le a b x y
    rw [List.zip_cons_cons, List.countP_cons]
    split_ifs at hab ⊢ with h₁ h₂ h₂
    all_goals first | omega | (exfalso; simp_all)

/-- Deleting the letters outside a subsequence. -/
theorem stepChain_of_sublist {z x : List α} (h : z <+ x) :
    StepChain IsEditStep (x.length - z.length) x z := by
  induction h with
  | slnil => exact .nil _
  | cons a h ih =>
    have hle := h.length_le
    exact (StepChain.cons (IsEditStep.delete_head a _) ih).of_eq (by simp only [length_cons]; omega)
  | cons_cons a h ih =>
    exact (ih.map (a :: ·) fun _ _ hs => hs.cons a).of_eq (by simp)

theorem editDist_le_of_sublist {z x : List α} (h : z <+ x) :
    editDist x z ≤ x.length - z.length :=
  editDist_le (stepChain_of_sublist h)

/-- Length of a longest common subsequence. -/
noncomputable def lcsLength (x y : List α) : ℕ :=
  sSup {n | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n}

theorem bddAbove_lcs (x y : List α) :
    BddAbove {n | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n} :=
  ⟨x.length, by rintro n ⟨z, hx, -, rfl⟩; exact hx.length_le⟩

theorem exists_lcs (x y : List α) :
    ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = lcsLength x y :=
  Nat.sSup_mem (s := {n | ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length = n})
    ⟨0, [], nil_sublist _, nil_sublist _, rfl⟩ (bddAbove_lcs x y)

theorem length_le_lcsLength {z x y : List α} (hx : z <+ x) (hy : z <+ y) :
    z.length ≤ lcsLength x y :=
  le_csSup (bddAbove_lcs x y) ⟨z, hx, hy, rfl⟩

theorem lcsLength_le_length_left (x y : List α) : lcsLength x y ≤ x.length := by
  obtain ⟨z, hx, -, hz⟩ := exists_lcs x y
  exact hz ▸ hx.length_le

theorem lcsLength_le_length_right (x y : List α) : lcsLength x y ≤ y.length := by
  obtain ⟨z, -, hy, hz⟩ := exists_lcs x y
  exact hz ▸ hy.length_le

theorem lcsLength_comm (x y : List α) : lcsLength x y = lcsLength y x := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨z', hy', hx', hz'⟩ := exists_lcs y x
  exact le_antisymm (hz ▸ length_le_lcsLength hy hx) (hz' ▸ length_le_lcsLength hx' hy')

@[simp] theorem lcsLength_self (x : List α) : lcsLength x x = x.length :=
  le_antisymm (lcsLength_le_length_left x x) (length_le_lcsLength (Sublist.refl x) (Sublist.refl x))

/-- A subsequence of `p ++ a :: q` loses at most one letter when `a` is removed. -/
theorem exists_sublist_of_sublist_insert {z p q : List α} {a : α} (h : z <+ p ++ a :: q) :
    ∃ z', z' <+ p ++ q ∧ z' <+ z ∧ z.length ≤ z'.length + 1 := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := List.sublist_append_iff.mp h
  rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨r, rfl, hr⟩
  · exact ⟨l₁ ++ l₂, h₁.append h₂, Sublist.refl _, by omega⟩
  · refine ⟨l₁ ++ r, h₁.append hr, (Sublist.refl l₁).append (sublist_cons_self a r), ?_⟩
    simp only [length_append, length_cons]
    omega

theorem IsEditStep.lcsLength_le {u v : List α} (h : IsEditStep u v) (y : List α) :
    lcsLength u y ≤ lcsLength v y + 1 := by
  obtain ⟨z, hzu, hzy, hz⟩ := exists_lcs u y
  rw [← hz]
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · have : z <+ p ++ a :: q :=
      hzu.trans ((Sublist.refl p).append (sublist_cons_self a q))
    exact (length_le_lcsLength this hzy).trans (Nat.le_add_right _ _)
  · obtain ⟨z', h₁, h₂, h₃⟩ := exists_sublist_of_sublist_insert hzu
    exact h₃.trans (Nat.add_le_add_right (length_le_lcsLength h₁ (h₂.trans hzy)) 1)
  · obtain ⟨z', h₁, h₂, h₃⟩ := exists_sublist_of_sublist_insert hzu
    have : z' <+ p ++ b :: q := h₁.trans ((Sublist.refl p).append (sublist_cons_self b q))
    exact h₃.trans (Nat.add_le_add_right (length_le_lcsLength this (h₂.trans hzy)) 1)

/-- `|y| ≤ lcs(x, y) + ed(x, y)`. -/
theorem length_le_lcsLength_add_editDist (x y : List α) :
    y.length ≤ lcsLength x y + editDist x y := by
  have := (stepChain_editDist x y).le_add (fun w => lcsLength w y)
    fun _ _ h => h.symm.lcsLength_le y
  simpa using this

theorem length_left_le_lcsLength_add_editDist (x y : List α) :
    x.length ≤ lcsLength x y + editDist x y := by
  rw [lcsLength_comm, editDist_comm]
  exact length_le_lcsLength_add_editDist y x

theorem max_length_le_lcsLength_add_editDist (x y : List α) :
    max x.length y.length ≤ lcsLength x y + editDist x y :=
  max_le (length_left_le_lcsLength_add_editDist x y) (length_le_lcsLength_add_editDist x y)

/-- Delete down to a longest common subsequence, then insert back up. -/
theorem editDist_add_two_mul_lcsLength_le (x y : List α) :
    editDist x y + 2 * lcsLength x y ≤ x.length + y.length := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  have h₁ := editDist_le_of_sublist hx
  have h₂ := editDist_le_of_sublist hy
  have h₃ := editDist_triangle x z y
  rw [editDist_comm z y] at h₃
  have := hx.length_le
  have := hy.length_le
  omega

/-- Equal lengths: `|x| - lcs ≤ ed ≤ 2 (|x| - lcs)`. -/
theorem length_sub_lcsLength_le_editDist (x y : List α) :
    x.length - lcsLength x y ≤ editDist x y := by
  have := length_left_le_lcsLength_add_editDist x y
  omega

theorem editDist_le_two_mul_length_sub_lcsLength {x y : List α} (h : x.length = y.length) :
    editDist x y ≤ 2 * (x.length - lcsLength x y) := by
  have := editDist_add_two_mul_lcsLength_le x y
  have := lcsLength_le_length_left x y
  omega

/-- A word map that sends each single edit to at most `w` edits expands `ed` by at most `w`. -/
theorem editDist_le_mul_of_step {γ : Type v} (g : List α → List γ) (w : ℕ)
    (hg : ∀ u v, IsEditStep u v → editDist (g u) (g v) ≤ w) (x y : List α) :
    editDist (g x) (g y) ≤ w * editDist x y := by
  suffices ∀ n x y, StepChain IsEditStep n x y → editDist (g x) (g y) ≤ w * n from
    this _ _ _ (stepChain_editDist x y)
  intro n x y h
  induction h with
  | nil x => simp
  | cons hxy _ ih =>
    calc editDist (g _) (g _) ≤ editDist (g _) (g _) + editDist (g _) (g _) :=
          editDist_triangle _ _ _
      _ ≤ w + w * _ := add_le_add (hg _ _ hxy) ih
      _ = w * (_ + 1) := by ring

/-- Letter-by-letter relabelling does not increase the edit distance. -/
theorem editDist_map_le {γ : Type v} (f : α → γ) (x y : List α) :
    editDist (x.map f) (y.map f) ≤ editDist x y := by
  simpa using editDist_le_mul_of_step (List.map f) 1
    (fun _ _ h => (h.map f).editDist_le_one) x y

/-- Block codes: replacing every letter by a codeword of length `w` expands `ed` by at most `w`. -/
theorem editDist_flatMap_le {γ : Type v} (c : α → List γ) (w : ℕ)
    (hc : ∀ a, (c a).length = w) (x y : List α) :
    editDist (x.flatMap c) (y.flatMap c) ≤ w * editDist x y := by
  refine editDist_le_mul_of_step (fun l => l.flatMap c) w ?_ x y
  intro u v h
  rcases h with ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, rfl, rfl⟩ | ⟨p, q, a, b, rfl, rfl⟩
  · simp only [flatMap_append, flatMap_cons]
    calc editDist (p.flatMap c ++ q.flatMap c) (p.flatMap c ++ (c a ++ q.flatMap c))
        ≤ editDist ([] ++ q.flatMap c) (c a ++ q.flatMap c) := editDist_append_left _ _ _
      _ ≤ editDist [] (c a) := editDist_append_right _ _ _
      _ = w := by simp [hc]
  · simp only [flatMap_append, flatMap_cons]
    calc editDist (p.flatMap c ++ (c a ++ q.flatMap c)) (p.flatMap c ++ q.flatMap c)
        ≤ editDist (c a ++ q.flatMap c) ([] ++ q.flatMap c) := editDist_append_left _ _ _
      _ ≤ editDist (c a) [] := editDist_append_right _ _ _
      _ = w := by simp [hc]
  · simp only [flatMap_append, flatMap_cons]
    calc editDist (p.flatMap c ++ (c a ++ q.flatMap c)) (p.flatMap c ++ (c b ++ q.flatMap c))
        ≤ editDist (c a ++ q.flatMap c) (c b ++ q.flatMap c) := editDist_append_left _ _ _
      _ ≤ editDist (c a) (c b) := editDist_append_right _ _ _
      _ ≤ max (c a).length (c b).length := editDist_le_max_length _ _
      _ = w := by simp [hc]

end EditStep

end TheoremOS.Combinatorics
