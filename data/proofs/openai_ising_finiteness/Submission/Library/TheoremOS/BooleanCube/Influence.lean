import Submission.Library.TheoremOS.BooleanCube.Fourier

/-!
# Influences on the Boolean cube

Coordinate flips, the operator `derivative i f x = (f x - f (flip i x)) / 2` (written `L_i f`
below), influence `Inf_i f = Pr[f x ≠ f (flip i x)]`, total influence, and their Fourier
formulas: `(L_i f)^ S = f̂ S` for `i ∈ S` and `0` otherwise; `Inf_i f = ∑_{S ∋ i} f̂ S²` and
`I f = ∑_S |S| f̂ S²` for ±1-valued `f`; total influence is the average sensitivity, is at most
the Fourier degree, and is at least the variance (Poincaré).

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Chapter 2 (Definitions 2.13, 2.16, 2.27, Proposition 2.19, Theorem 2.20, Theorem 2.38,
Proposition 2.28). Textbook material.

Bridges: `flip i x = Function.update x i (!(x i))`, the usual "flip one coordinate";
`sensitivityAt f x` counts coordinates whose flip changes `f x`. Notation: `derivative` is
O'Donnell's Laplacian `L_i` (it keeps `f̂ S` for `S ∋ i`), not his derivative `D_i` (which sends
`f̂ S` to `S \ {i}`); `D_i` is `coordDerivative` in `Hypercontractivity`, and
`L_i f x = sign (x i) · D_i f x`. Both square to the same influence for ±1-valued `f`.
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Flip coordinate `i`. -/
def flip (i : ι) (x : ι → Bool) : ι → Bool := Function.update x i (!(x i))

@[simp] lemma flip_apply_self (i : ι) (x : ι → Bool) : flip i x i = !(x i) := by simp [flip]

lemma flip_apply_of_ne {i j : ι} (h : j ≠ i) (x : ι → Bool) : flip i x j = x j := by
  simp [flip, Function.update_of_ne h]

@[simp] lemma flip_flip (i : ι) (x : ι → Bool) : flip i (flip i x) = x := by
  funext j; by_cases h : j = i
  · subst h; simp
  · simp [flip_apply_of_ne h]

lemma flip_ne (i : ι) (x : ι → Bool) : flip i x ≠ x := fun h => by
  have := congrFun h i; simp at this

/-- `flip i` as an involutive equivalence. -/
def flipEquiv (i : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flip i
  invFun := flip i
  left_inv := flip_flip i
  right_inv := flip_flip i

lemma character_flip (S : Finset ι) (i : ι) (x : ι → Bool) :
    character S (flip i x) = if i ∈ S then -character S x else character S x := by
  split_ifs with h
  · rw [character, ← mul_prod_erase S _ h, character, ← mul_prod_erase S _ h, flip_apply_self, sign_not]
    have : ∏ j ∈ S.erase i, sign (flip i x j) = ∏ j ∈ S.erase i, sign (x j) :=
      prod_congr rfl fun j hj => by rw [flip_apply_of_ne (ne_of_mem_erase hj)]
    rw [this]; ring
  · exact prod_congr rfl fun j hj => by rw [flip_apply_of_ne (fun e : j = i => h (e ▸ hj))]

/-- The coordinate-`i` Laplacian `L_i f x = (f x - f (flip i x)) / 2` (O'Donnell's `L_i`, not
`D_i`; see `coordDerivative` for `D_i`). -/
def derivative (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ := (f x - f (flip i x)) / 2

lemma IsBooleanValued.derivative_sq {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) (i : ι) (x : ι → Bool) :
    derivative i f x ^ 2 = if f x ≠ f (flip i x) then 1 else 0 := by
  unfold derivative
  rcases hf x with h | h <;> rcases hf (flip i x) with h' | h' <;> rw [h, h'] <;> norm_num

variable [Fintype ι]

lemma average_comp_flip (i : ι) (f : (ι → Bool) → ℝ) : average (fun x => f (flip i x)) = average f :=
  average_comp_equiv (flipEquiv i) f

theorem fourierCoeff_derivative (i : ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (derivative i f) S = if i ∈ S then fourierCoeff f S else 0 := by
  have hflip : average (fun x => f (flip i x) * character S x) =
      if i ∈ S then -fourierCoeff f S else fourierCoeff f S := by
    rw [← average_comp_flip i (fun x => f (flip i x) * character S x)]
    by_cases h : i ∈ S
    · simp only [flip_flip, character_flip, h, ite_true, fourierCoeff]
      calc average (fun x => f x * -character S x) = average (fun x => (-1) * (f x * character S x)) :=
            average_congr fun x => by ring
        _ = -average (fun x => f x * character S x) := by rw [average_const_mul]; ring
    · simp only [flip_flip, character_flip, h, ite_false, fourierCoeff]
  have hsplit : fourierCoeff (derivative i f) S =
      (fourierCoeff f S - average (fun x => f (flip i x) * character S x)) / 2 := by
    rw [fourierCoeff, fourierCoeff, ← average_sub, eq_div_iff two_ne_zero, ← average_mul_const]
    exact average_congr fun x => by simp only [derivative]; ring
  rw [hsplit, hflip]
  split_ifs <;> ring

/-- `Inf_i f`: the probability that flipping coordinate `i` changes `f`. -/
def influence (i : ι) (f : (ι → Bool) → ℝ) : ℝ := average fun x => if f x ≠ f (flip i x) then 1 else 0

/-- Total influence `I f = ∑_i Inf_i f`. -/
def totalInfluence (f : (ι → Bool) → ℝ) : ℝ := ∑ i, influence i f

lemma influence_nonneg (i : ι) (f : (ι → Bool) → ℝ) : 0 ≤ influence i f := by
  unfold influence; exact average_nonneg fun x => by split_ifs <;> norm_num

theorem IsBooleanValued.influence_eq_average {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) (i : ι) :
    influence i f = average (fun x => derivative i f x ^ 2) := by
  unfold influence
  exact average_congr fun x => by rw [hf.derivative_sq i x]

/-- `Inf_i f = ∑_{S ∋ i} f̂ S²` for ±1-valued `f`. -/
theorem IsBooleanValued.influence_eq_sum {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) (i : ι) :
    influence i f = ∑ S ∈ univ.filter (fun S : Finset ι => i ∈ S), fourierCoeff f S ^ 2 := by
  rw [hf.influence_eq_average, parseval, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  rw [fourierCoeff_derivative]; split_ifs <;> simp

/-- `I f = ∑_S |S| f̂ S²` for ±1-valued `f`. -/
theorem IsBooleanValued.totalInfluence_eq_sum {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    totalInfluence f = ∑ S : Finset ι, (S.card : ℝ) * fourierCoeff f S ^ 2 := by
  unfold totalInfluence
  simp only [hf.influence_eq_sum, sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter, univ_inter]

/-- Total influence is at most the Fourier degree. -/
theorem IsBooleanValued.totalInfluence_le_degree {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    totalInfluence f ≤ degree f := by
  rw [hf.totalInfluence_eq_sum]
  calc ∑ S : Finset ι, (S.card : ℝ) * fourierCoeff f S ^ 2
      ≤ ∑ S : Finset ι, (degree f : ℝ) * fourierCoeff f S ^ 2 := by
        refine sum_le_sum fun S _ => ?_
        by_cases h : fourierCoeff f S = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_degree h) (sq_nonneg _)
    _ = degree f := by rw [← mul_sum, hf.sum_fourierCoeff_sq, mul_one]

/-- Poincaré inequality: `Var f ≤ I f` for ±1-valued `f`. -/
theorem IsBooleanValued.variance_le_totalInfluence {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    variance f ≤ totalInfluence f := by
  rw [variance_eq_sum, hf.totalInfluence_eq_sum, ← add_sum_erase _ _ (mem_univ (∅ : Finset ι))]
  simp only [card_empty, Nat.cast_zero, zero_mul, zero_add]
  refine sum_le_sum fun S hS => ?_
  have : (1 : ℝ) ≤ S.card := by
    exact_mod_cast card_pos.2 (nonempty_iff_ne_empty.2 (ne_of_mem_erase hS))
  exact le_mul_of_one_le_left (sq_nonneg _) this

/-- The number of coordinates whose flip changes `f x`. -/
def sensitivityAt (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℕ := (univ.filter fun i => f x ≠ f (flip i x)).card

/-- Total influence is the average sensitivity. -/
theorem totalInfluence_eq_average_sensitivity (f : (ι → Bool) → ℝ) :
    totalInfluence f = average (fun x => (sensitivityAt f x : ℝ)) := by
  unfold totalInfluence influence sensitivityAt
  rw [← average_sum]
  exact average_congr fun x => by simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end

end TheoremOS.BooleanCube
