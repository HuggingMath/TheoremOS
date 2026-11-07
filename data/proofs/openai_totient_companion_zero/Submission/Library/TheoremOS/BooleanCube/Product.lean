import Submission.Library.TheoremOS.BooleanCube.Relabel

/-!
# Products of functions of disjoint sets of coordinates

For `f` on `ι`-cubes and `g` on `κ`-cubes, `tensor f g x = f (leftPart x) * g (rightPart x)` on
`(ι ⊕ κ)`-cubes. Its Fourier coefficients factor, `(f ⊗ g)^ U = f̂ U.toLeft · ĝ U.toRight`; the
degree of a product of nonzero functions is the sum of the degrees; the level-one coefficients are
`(f ⊗ g)^ {inl i} = f̂ {i} · E g` and `(f ⊗ g)^ {inr k} = E f · ĝ {k}`; influences and total
influence add when the factors never vanish (e.g. ±1-valued). `tensorFin f g` is the same product
on `Fin (m + n)`-cubes (first `m` coordinates to `f`, last `n` to `g`), through `relabel`.

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Chapter 1 (the Fourier expansion of a product of functions of disjoint variables is the product
of their expansions) and Chapter 2 (influences). Textbook material.

Bridges: `leftPart x i = x (Sum.inl i)`, `rightPart x k = x (Sum.inr k)`, `splitEquiv` is
`Equiv.sumArrowEquivProdArrow`; `tensorFin_apply` reads `tensorFin f g x` through
`Fin.castAdd`/`Fin.natAdd`.
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

variable {ι κ : Type*}

/-- The `ι`-coordinates of a point of the `(ι ⊕ κ)`-cube. -/
def leftPart (x : ι ⊕ κ → Bool) : ι → Bool := fun i => x (Sum.inl i)

/-- The `κ`-coordinates of a point of the `(ι ⊕ κ)`-cube. -/
def rightPart (x : ι ⊕ κ → Bool) : κ → Bool := fun k => x (Sum.inr k)

/-- `x ↦ (leftPart x, rightPart x)`. -/
def splitEquiv : (ι ⊕ κ → Bool) ≃ (ι → Bool) × (κ → Bool) := Equiv.sumArrowEquivProdArrow ι κ Bool

@[simp] lemma splitEquiv_apply (x : ι ⊕ κ → Bool) : splitEquiv x = (leftPart x, rightPart x) := rfl

/-- `(f ⊗ g) x = f (leftPart x) · g (rightPart x)`. -/
def tensor (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) (x : ι ⊕ κ → Bool) : ℝ :=
  f (leftPart x) * g (rightPart x)

lemma tensor_apply (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) (x : ι ⊕ κ → Bool) :
    tensor f g x = f (leftPart x) * g (rightPart x) := rfl

lemma character_sum (U : Finset (ι ⊕ κ)) (x : ι ⊕ κ → Bool) :
    character U x = character U.toLeft (leftPart x) * character U.toRight (rightPart x) := by
  conv_lhs => rw [← toLeft_disjSum_toRight (u := U)]
  simp only [character, prod_disjSum, leftPart, rightPart]

lemma IsBooleanValued.apply_ne_zero {α : Type*} {f : α → ℝ} (hf : IsBooleanValued f) (x : α) : f x ≠ 0 := by
  rcases hf x with h | h <;> rw [h] <;> norm_num

lemma IsBooleanValued.ne_zero {α : Type*} [Nonempty α] {f : α → ℝ} (hf : IsBooleanValued f) : f ≠ 0 := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  exact hf.apply_ne_zero a (by rw [h, Pi.zero_apply])

lemma IsBooleanValued.tensor {f : (ι → Bool) → ℝ} {g : (κ → Bool) → ℝ} (hf : IsBooleanValued f)
    (hg : IsBooleanValued g) : IsBooleanValued (BooleanCube.tensor f g) := fun x => by
  unfold BooleanCube.tensor
  rcases hf (leftPart x) with h | h <;> rcases hg (rightPart x) with h' | h' <;> rw [h, h'] <;> norm_num

@[simp] lemma toLeft_singleton_inl (i : ι) : ({Sum.inl i} : Finset (ι ⊕ κ)).toLeft = {i} := by ext; simp
@[simp] lemma toRight_singleton_inl (i : ι) : ({Sum.inl i} : Finset (ι ⊕ κ)).toRight = ∅ := by ext; simp
@[simp] lemma toLeft_singleton_inr (k : κ) : ({Sum.inr k} : Finset (ι ⊕ κ)).toLeft = ∅ := by ext; simp
@[simp] lemma toRight_singleton_inr (k : κ) : ({Sum.inr k} : Finset (ι ⊕ κ)).toRight = {k} := by ext; simp

section Flip

variable [DecidableEq ι] [DecidableEq κ]

lemma leftPart_flip_inl (i : ι) (x : ι ⊕ κ → Bool) : leftPart (flip (Sum.inl i) x) = flip i (leftPart x) := by
  funext j
  by_cases h : j = i
  · subst h; simp [leftPart]
  · rw [flip_apply_of_ne h]; unfold leftPart
    rw [flip_apply_of_ne (show (Sum.inl j : ι ⊕ κ) ≠ Sum.inl i from fun e => h (Sum.inl_injective e))]

lemma rightPart_flip_inl (i : ι) (x : ι ⊕ κ → Bool) : rightPart (flip (Sum.inl i) x) = rightPart x := by
  funext k; unfold rightPart; exact flip_apply_of_ne Sum.inr_ne_inl x

lemma leftPart_flip_inr (k : κ) (x : ι ⊕ κ → Bool) : leftPart (flip (Sum.inr k) x) = leftPart x := by
  funext i; unfold leftPart; exact flip_apply_of_ne Sum.inl_ne_inr x

lemma rightPart_flip_inr (k : κ) (x : ι ⊕ κ → Bool) : rightPart (flip (Sum.inr k) x) = flip k (rightPart x) := by
  funext j
  by_cases h : j = k
  · subst h; simp [rightPart]
  · rw [flip_apply_of_ne h]; unfold rightPart
    rw [flip_apply_of_ne (show (Sum.inr j : ι ⊕ κ) ≠ Sum.inr k from fun e => h (Sum.inr_injective e))]

end Flip

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma average_tensor_split (F : (ι → Bool) → ℝ) (G : (κ → Bool) → ℝ) :
    (average fun x : ι ⊕ κ → Bool => F (leftPart x) * G (rightPart x)) = average F * average G := by
  have h := average_comp_equiv_of_equiv (splitEquiv (ι := ι) (κ := κ)) fun p => F p.1 * G p.2
  simp only [splitEquiv_apply] at h
  rw [h]
  unfold average
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type]
  simp only [← mul_sum, ← sum_mul]
  ring

/-- `(f ⊗ g)^ U = f̂ U.toLeft · ĝ U.toRight`. -/
theorem fourierCoeff_tensor (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) (U : Finset (ι ⊕ κ)) :
    fourierCoeff (tensor f g) U = fourierCoeff f U.toLeft * fourierCoeff g U.toRight := by
  unfold fourierCoeff
  rw [← average_tensor_split]
  refine average_congr fun x => ?_
  rw [tensor, character_sum]; ring

omit [Fintype κ] [DecidableEq κ] in
/-- A nonzero function has a nonzero coefficient on a set of size equal to its degree. -/
lemma exists_card_eq_degree {f : (ι → Bool) → ℝ} (hf : f ≠ 0) :
    ∃ S, fourierCoeff f S ≠ 0 ∧ S.card = degree f := by
  have hne : (univ.filter fun S : Finset ι => fourierCoeff f S ≠ 0).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    apply hf
    funext x
    rw [fourier_expansion f x, Pi.zero_apply]
    refine sum_eq_zero fun S _ => ?_
    have : fourierCoeff f S = 0 := by
      by_contra hS
      have hmem : S ∈ univ.filter fun S : Finset ι => fourierCoeff f S ≠ 0 := mem_filter.2 ⟨mem_univ S, hS⟩
      rw [h] at hmem; exact absurd hmem (notMem_empty S)
    rw [this, zero_mul]
  obtain ⟨S, hS, h⟩ := exists_mem_eq_sup _ hne card
  exact ⟨S, (mem_filter.1 hS).2, h.symm⟩

theorem degree_tensor_le (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) :
    degree (tensor f g) ≤ degree f + degree g := by
  rw [degree_le_iff]
  intro U hU
  rw [fourierCoeff_tensor] at hU
  rw [← card_toLeft_add_card_toRight (u := U)]
  exact Nat.add_le_add (card_le_degree (left_ne_zero_of_mul hU)) (card_le_degree (right_ne_zero_of_mul hU))

/-- `deg (f ⊗ g) = deg f + deg g` for nonzero `f`, `g`. -/
theorem degree_tensor {f : (ι → Bool) → ℝ} {g : (κ → Bool) → ℝ} (hf : f ≠ 0) (hg : g ≠ 0) :
    degree (tensor f g) = degree f + degree g := by
  refine le_antisymm (degree_tensor_le f g) ?_
  obtain ⟨S, hS, hScard⟩ := exists_card_eq_degree hf
  obtain ⟨T, hT, hTcard⟩ := exists_card_eq_degree hg
  have hU : fourierCoeff (tensor f g) (S.disjSum T) ≠ 0 := by
    rw [fourierCoeff_tensor, toLeft_disjSum, toRight_disjSum]; exact mul_ne_zero hS hT
  have := card_le_degree hU
  rwa [card_disjSum, hScard, hTcard] at this

lemma fourierCoeff_tensor_inl (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) (i : ι) :
    fourierCoeff (tensor f g) {Sum.inl i} = fourierCoeff f {i} * average g := by
  rw [fourierCoeff_tensor, toLeft_singleton_inl, toRight_singleton_inl, fourierCoeff_empty]

lemma fourierCoeff_tensor_inr (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) (k : κ) :
    fourierCoeff (tensor f g) {Sum.inr k} = average f * fourierCoeff g {k} := by
  rw [fourierCoeff_tensor, toLeft_singleton_inr, toRight_singleton_inr, fourierCoeff_empty]

/-- `∑_u (f ⊗ g)^ {u} = (∑_i f̂ {i}) E g + E f (∑_k ĝ {k})`. -/
theorem sum_fourierCoeff_tensor_singleton (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) :
    ∑ u, fourierCoeff (tensor f g) {u} =
      (∑ i, fourierCoeff f {i}) * average g + average f * ∑ k, fourierCoeff g {k} := by
  rw [Fintype.sum_sum_type]
  simp only [fourierCoeff_tensor_inl, fourierCoeff_tensor_inr, ← sum_mul, ← mul_sum]

theorem sum_abs_fourierCoeff_tensor_singleton (f : (ι → Bool) → ℝ) (g : (κ → Bool) → ℝ) :
    ∑ u, |fourierCoeff (tensor f g) {u}| =
      (∑ i, |fourierCoeff f {i}|) * |average g| + |average f| * ∑ k, |fourierCoeff g {k}| := by
  rw [Fintype.sum_sum_type]
  simp only [fourierCoeff_tensor_inl, fourierCoeff_tensor_inr, abs_mul, ← sum_mul, ← mul_sum]

theorem influence_tensor_inl (f : (ι → Bool) → ℝ) {g : (κ → Bool) → ℝ} (hg : ∀ y, g y ≠ 0) (i : ι) :
    influence (Sum.inl i) (tensor f g) = influence i f := by
  unfold influence
  have h := average_tensor_split (fun y : ι → Bool => if f y ≠ f (flip i y) then (1 : ℝ) else 0)
    (fun _ : κ → Bool => (1 : ℝ))
  rw [average_const, mul_one] at h
  rw [← h]
  refine average_congr fun x => ?_
  simp only [tensor, leftPart_flip_inl, rightPart_flip_inl, ne_eq, mul_left_inj' (hg _), mul_one]

theorem influence_tensor_inr {f : (ι → Bool) → ℝ} (hf : ∀ y, f y ≠ 0) (g : (κ → Bool) → ℝ) (k : κ) :
    influence (Sum.inr k) (tensor f g) = influence k g := by
  unfold influence
  have h := average_tensor_split (fun _ : ι → Bool => (1 : ℝ))
    (fun y : κ → Bool => if g y ≠ g (flip k y) then (1 : ℝ) else 0)
  rw [average_const, one_mul] at h
  rw [← h]
  refine average_congr fun x => ?_
  simp only [tensor, leftPart_flip_inr, rightPart_flip_inr, ne_eq, mul_right_inj' (hf _), one_mul]

/-- `I (f ⊗ g) = I f + I g` when neither factor vanishes. -/
theorem totalInfluence_tensor {f : (ι → Bool) → ℝ} {g : (κ → Bool) → ℝ} (hf : ∀ y, f y ≠ 0)
    (hg : ∀ y, g y ≠ 0) : totalInfluence (tensor f g) = totalInfluence f + totalInfluence g := by
  unfold totalInfluence
  rw [Fintype.sum_sum_type]
  simp only [influence_tensor_inl f hg, influence_tensor_inr hf g]

theorem IsBooleanValued.totalInfluence_tensor {f : (ι → Bool) → ℝ} {g : (κ → Bool) → ℝ}
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    totalInfluence (BooleanCube.tensor f g) = totalInfluence f + totalInfluence g :=
  BooleanCube.totalInfluence_tensor hf.apply_ne_zero hg.apply_ne_zero

theorem IsBooleanValued.degree_tensor {f : (ι → Bool) → ℝ} {g : (κ → Bool) → ℝ}
    (hf : IsBooleanValued f) (hg : IsBooleanValued g) :
    degree (BooleanCube.tensor f g) = degree f + degree g :=
  BooleanCube.degree_tensor hf.ne_zero hg.ne_zero

end

/-! ### The same product on `Fin (m + n)` -/

section Fin

variable {m n : ℕ}

/-- `tensorFin f g` on `Fin (m + n)`-cubes: the first `m` coordinates go to `f`, the last `n` to `g`. -/
noncomputable def tensorFin (f : (Fin m → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) : (Fin (m + n) → Bool) → ℝ :=
  relabel finSumFinEquiv.symm (tensor f g)

lemma tensorFin_apply (f : (Fin m → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) (x : Fin (m + n) → Bool) :
    tensorFin f g x = f (fun i => x (Fin.castAdd n i)) * g (fun k => x (Fin.natAdd m k)) := by
  rfl

lemma IsBooleanValued.tensorFin {f : (Fin m → Bool) → ℝ} {g : (Fin n → Bool) → ℝ} (hf : IsBooleanValued f)
    (hg : IsBooleanValued g) : IsBooleanValued (BooleanCube.tensorFin f g) :=
  (hf.tensor hg).relabel _

theorem degree_tensorFin {f : (Fin m → Bool) → ℝ} {g : (Fin n → Bool) → ℝ} (hf : f ≠ 0) (hg : g ≠ 0) :
    degree (tensorFin f g) = degree f + degree g := by
  rw [tensorFin, degree_relabel, degree_tensor hf hg]

theorem totalInfluence_tensorFin {f : (Fin m → Bool) → ℝ} {g : (Fin n → Bool) → ℝ} (hf : ∀ y, f y ≠ 0)
    (hg : ∀ y, g y ≠ 0) : totalInfluence (tensorFin f g) = totalInfluence f + totalInfluence g := by
  rw [tensorFin, totalInfluence_relabel, totalInfluence_tensor hf hg]

theorem sum_fourierCoeff_tensorFin_singleton (f : (Fin m → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) :
    ∑ i, fourierCoeff (tensorFin f g) {i} =
      (∑ i, fourierCoeff f {i}) * average g + average f * ∑ k, fourierCoeff g {k} :=
  (sum_fourierCoeff_relabel_singleton finSumFinEquiv.symm (tensor f g) id).trans
    (sum_fourierCoeff_tensor_singleton f g)

theorem sum_abs_fourierCoeff_tensorFin_singleton (f : (Fin m → Bool) → ℝ) (g : (Fin n → Bool) → ℝ) :
    ∑ i, |fourierCoeff (tensorFin f g) {i}| =
      (∑ i, |fourierCoeff f {i}|) * |average g| + |average f| * ∑ k, |fourierCoeff g {k}| :=
  (sum_fourierCoeff_relabel_singleton finSumFinEquiv.symm (tensor f g) fun t => |t|).trans
    (sum_abs_fourierCoeff_tensor_singleton f g)

end Fin

end TheoremOS.BooleanCube
