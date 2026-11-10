import Submission.Library.TheoremOS.BooleanCube.Influence

/-!
# Level-one Fourier coefficients

The degree-one coefficients `f̂ {i}` of a function on the Boolean cube: the formula
`f̂ {i} = E[L_i f x · sign (x i)]` with `L_i = derivative i`; the bounds `|f̂ {i}| ≤ Inf_i f`,
`∑ i |f̂ {i}| ≤ I f ≤ deg f` for ±1-valued `f`; the level-one weight `W¹ f = ∑ i f̂ {i}² ≤ E[f²]`;
the Cauchy–Schwarz bound `∑ i |f̂ {i}| ≤ √|ι| · √(W¹ f) ≤ √|ι|`; and, for monotone ±1-valued `f`,
the equality `f̂ {i} = Inf_i f`, so `∑ i f̂ {i} = I f`.

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Chapter 2 (Proposition 2.21 for monotone functions, Exercise 2.5/Proposition 2.22 style level-one
bounds) and Chapter 5 (level-one weight). Textbook material.

Bridges: with `sign false = 1`, `sign true = -1` the order on `ι → Bool` (`false < true`) is
reversed, so O'Donnell's "monotone" (`x ≤ y ⇒ f x ≤ f y` on `{±1}ⁿ`) is `Antitone f` here.
`(∀ x, f x = -1 ∨ f x = 1)` is `IsBooleanValued f` (`isBooleanValued_iff`). The count form
`I f = ∑ i #{x | f x ≠ f (flip i x)} / 2ⁿ` is `totalInfluence_eq_sum_card` (and the `Fin n`
version `totalInfluence_fin_eq_sum_card`).
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*}

lemma isBooleanValued_iff {α : Type*} {f : α → ℝ} :
    (∀ x, f x = -1 ∨ f x = 1) ↔ IsBooleanValued f :=
  ⟨fun h x => (h x).symm, fun h x => (h x).symm⟩

@[simp] lemma abs_sign_bool (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

lemma abs_average_le {α : Type*} [Fintype α] (f : α → ℝ) : |average f| ≤ average fun x => |f x| := by
  unfold average
  rw [abs_mul, abs_inv, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (inv_nonneg.2 (Nat.cast_nonneg _))

variable [DecidableEq ι]

lemma IsBooleanValued.abs_derivative {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) (i : ι) (x : ι → Bool) :
    |derivative i f x| = if f x ≠ f (flip i x) then 1 else 0 := by
  unfold derivative
  rcases hf x with h | h <;> rcases hf (flip i x) with h' | h' <;> rw [h, h'] <;> norm_num

variable [Fintype ι]

/-- `f̂ {i} = E[L_i f x · sign (x i)]`, where `L_i f = derivative i f`. -/
theorem fourierCoeff_singleton_eq (i : ι) (f : (ι → Bool) → ℝ) :
    fourierCoeff f {i} = average fun x => derivative i f x * sign (x i) := by
  have h := fourierCoeff_derivative i f {i}
  simp only [mem_singleton_self, ↓reduceIte] at h
  rw [← h, fourierCoeff]
  exact average_congr fun x => by rw [character_singleton]

/-- `|f̂ {i}| ≤ Inf_i f` for ±1-valued `f`. -/
theorem IsBooleanValued.abs_fourierCoeff_singleton_le {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f)
    (i : ι) : |fourierCoeff f {i}| ≤ influence i f := by
  rw [fourierCoeff_singleton_eq]
  refine (abs_average_le _).trans (le_of_eq ?_)
  unfold influence
  exact average_congr fun x => by rw [abs_mul, abs_sign_bool, mul_one, hf.abs_derivative]

/-- `∑ i |f̂ {i}| ≤ I f` for ±1-valued `f`. -/
theorem IsBooleanValued.sum_abs_fourierCoeff_singleton_le {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    ∑ i, |fourierCoeff f {i}| ≤ totalInfluence f :=
  sum_le_sum fun i _ => hf.abs_fourierCoeff_singleton_le i

/-- `∑ i |f̂ {i}| ≤ deg f` for ±1-valued `f`. -/
theorem IsBooleanValued.sum_abs_fourierCoeff_singleton_le_degree {f : (ι → Bool) → ℝ}
    (hf : IsBooleanValued f) : ∑ i, |fourierCoeff f {i}| ≤ degree f :=
  hf.sum_abs_fourierCoeff_singleton_le.trans hf.totalInfluence_le_degree

lemma sum_fourierCoeff_singleton_le_sum_abs (f : (ι → Bool) → ℝ) :
    ∑ i, fourierCoeff f {i} ≤ ∑ i, |fourierCoeff f {i}| :=
  sum_le_sum fun _ _ => le_abs_self _

/-- The level-one Fourier weight `W¹ f = ∑ i f̂ {i}²`. -/
def levelOneWeight (f : (ι → Bool) → ℝ) : ℝ := ∑ i, fourierCoeff f {i} ^ 2

lemma levelOneWeight_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ levelOneWeight f :=
  sum_nonneg fun _ _ => sq_nonneg _

lemma levelOneWeight_eq_sum_card_eq_one (f : (ι → Bool) → ℝ) :
    levelOneWeight f = ∑ S ∈ univ.filter (fun S : Finset ι => S.card = 1), fourierCoeff f S ^ 2 := by
  have himage : univ.filter (fun S : Finset ι => S.card = 1) = univ.image fun i : ι => ({i} : Finset ι) := by
    ext S; simp [card_eq_one, eq_comm]
  rw [himage, sum_image (singleton_injective.injOn), levelOneWeight]

/-- `W¹ f ≤ E[f²]`. -/
theorem levelOneWeight_le_average_sq (f : (ι → Bool) → ℝ) :
    levelOneWeight f ≤ average fun x => f x ^ 2 := by
  rw [levelOneWeight_eq_sum_card_eq_one, parseval]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => sq_nonneg _

theorem IsBooleanValued.levelOneWeight_le_one {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    levelOneWeight f ≤ 1 := by
  have h := levelOneWeight_le_average_sq f
  rwa [average_congr hf.sq_eq_one, average_const] at h

/-- Cauchy–Schwarz: `∑ i |f̂ {i}| ≤ √|ι| · √(W¹ f)`. -/
theorem sum_abs_fourierCoeff_singleton_le_sqrt (f : (ι → Bool) → ℝ) :
    ∑ i, |fourierCoeff f {i}| ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (levelOneWeight f) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1 : ℝ)) fun i => |fourierCoeff f {i}|
  simp only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] at h
  exact h

theorem IsBooleanValued.sum_abs_fourierCoeff_singleton_le_sqrt_card {f : (ι → Bool) → ℝ}
    (hf : IsBooleanValued f) : ∑ i, |fourierCoeff f {i}| ≤ Real.sqrt (Fintype.card ι) := by
  refine (sum_abs_fourierCoeff_singleton_le_sqrt f).trans ?_
  calc Real.sqrt (Fintype.card ι) * Real.sqrt (levelOneWeight f)
      ≤ Real.sqrt (Fintype.card ι) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one]; exact hf.levelOneWeight_le_one
    _ = Real.sqrt (Fintype.card ι) := mul_one _

/-- For antitone (O'Donnell: monotone) ±1-valued `f`, `f̂ {i} = Inf_i f`. -/
theorem IsBooleanValued.fourierCoeff_singleton_eq_influence_of_antitone {f : (ι → Bool) → ℝ}
    (hf : IsBooleanValued f) (hmono : Antitone f) (i : ι) : fourierCoeff f {i} = influence i f := by
  have key : ∀ y : ι → Bool, y i = true → f y ≤ f (flip i y) := by
    intro y hy
    apply hmono
    intro j
    by_cases hj : j = i
    · subst hj; simp [hy]
    · rw [flip_apply_of_ne hj]
  rw [fourierCoeff_singleton_eq, influence]
  refine average_congr fun x => ?_
  unfold derivative
  cases hx : x i
  · have hle := key (flip i x) (by simp [hx])
    rw [flip_flip] at hle
    rcases hf x with h | h <;> rcases hf (flip i x) with h' | h' <;> rw [h, h'] at hle ⊢ <;>
      first | (norm_num at hle; done) | norm_num
  · have hle := key x hx
    rcases hf x with h | h <;> rcases hf (flip i x) with h' | h' <;> rw [h, h'] at hle ⊢ <;>
      first | (norm_num at hle; done) | norm_num

theorem IsBooleanValued.sum_fourierCoeff_singleton_eq_totalInfluence_of_antitone {f : (ι → Bool) → ℝ}
    (hf : IsBooleanValued f) (hmono : Antitone f) : ∑ i, fourierCoeff f {i} = totalInfluence f :=
  sum_congr rfl fun i _ => hf.fourierCoeff_singleton_eq_influence_of_antitone hmono i

/-- `I f = ∑ i #{x | f x ≠ f (flip i x)} / 2^|ι|`. -/
theorem totalInfluence_eq_sum_card (f : (ι → Bool) → ℝ) :
    totalInfluence f =
      ∑ i, ((univ.filter fun x : ι → Bool => f x ≠ f (flip i x)).card : ℝ) / 2 ^ Fintype.card ι := by
  unfold totalInfluence influence average
  refine sum_congr rfl fun i _ => ?_
  rw [sum_boole, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, inv_mul_eq_div]

theorem totalInfluence_fin_eq_sum_card {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    totalInfluence f = ∑ i, ((univ.filter fun x : Fin n → Bool => f x ≠ f (flip i x)).card : ℝ) / 2 ^ n := by
  rw [totalInfluence_eq_sum_card, Fintype.card_fin]

end

end TheoremOS.BooleanCube
