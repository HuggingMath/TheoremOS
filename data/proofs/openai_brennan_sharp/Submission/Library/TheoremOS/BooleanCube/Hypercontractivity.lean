import Submission.Library.TheoremOS.BooleanCube.Influence

/-!
# Hypercontractivity on the Boolean cube: the Bonami lemma

For `f : (ι → Bool) → ℝ` of Fourier degree at most `d`: the Bonami lemma
`E[f⁴] ≤ 9^d E[f²]²`; the moment comparison `E[f²] ≤ 9^d E[|f|]²`; anti-concentration
`(1 - θ)² / 9^d ≤ Pr[f² > θ E[f²]]` for `0 ≤ θ ≤ 1` and `f ≠ 0`; and `Pr[f > 0] ≥ 1 / (4 · 9^d)`
when also `E[f] = 0`. Along the way: the decomposition `f = x_i · D_i f + E_i f` into parts
not depending on coordinate `i` (`coordDerivative`, `coordAverage`) with their Fourier
coefficients, Cauchy–Schwarz for averages, and the Paley–Zygmund inequality for averages.

Sources: A. Bonami, Étude des coefficients de Fourier des fonctions de `L^p(G)`, Ann. Inst.
Fourier 20 (1970); R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
2014, Chapter 9 (the Bonami Lemma, its proof by induction on coordinates, and the
anti-concentration corollaries via Paley–Zygmund). Textbook material; nothing here is specific
to a benchmark problem.

Bridges: `average` is the uniform expectation and `average (fun x => if P x then 1 else 0)` is
`Pr[P]`; `degree f ≤ d` is "Fourier degree at most `d`" (`degree_le_iff`); a multilinear real
polynomial `p` evaluated at `±1` points is `evalSign p` with `degree (evalSign p) = p.totalDegree`
(`degree_evalSign_of_multilinear`).
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

section Average

variable {α : Type*} [Fintype α]

lemma average_neg (f : α → ℝ) : average (fun x => -f x) = -average f := by
  rw [show (fun x => -f x) = fun x => (-1) * f x from funext fun x => by ring, average_const_mul]
  ring

/-- Cauchy–Schwarz for averages, weighted form. -/
lemma average_sq_le_mul {r u v : α → ℝ} (hu : ∀ x, 0 ≤ u x) (hv : ∀ x, 0 ≤ v x)
    (h : ∀ x, r x ^ 2 ≤ u x * v x) : average r ^ 2 ≤ average u * average v := by
  have key := sum_sq_le_sum_mul_sum_of_sq_le_mul univ (fun x _ => hu x) (fun x _ => hv x)
    (fun x _ => h x)
  simp only [average]
  rw [mul_pow, show ((Fintype.card α : ℝ)⁻¹ * ∑ x, u x) * ((Fintype.card α : ℝ)⁻¹ * ∑ x, v x) =
    (Fintype.card α : ℝ)⁻¹ ^ 2 * ((∑ x, u x) * ∑ x, v x) by ring]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- Cauchy–Schwarz for averages: `E[f g]² ≤ E[f²] E[g²]`. -/
lemma average_mul_sq_le (f g : α → ℝ) :
    average (fun x => f x * g x) ^ 2 ≤ average (fun x => f x ^ 2) * average (fun x => g x ^ 2) :=
  average_sq_le_mul (fun x => sq_nonneg (f x)) (fun x => sq_nonneg (g x))
    (fun x => (mul_pow (f x) (g x) 2).le)

lemma average_sq_pos {f : α → ℝ} (h : ∃ x, f x ≠ 0) : 0 < average (fun x => f x ^ 2) := by
  obtain ⟨x, hx⟩ := h
  have : Nonempty α := ⟨x⟩
  have hsum : 0 < ∑ y, f y ^ 2 :=
    sum_pos' (fun y _ => sq_nonneg (f y)) ⟨x, mem_univ x, by positivity⟩
  exact mul_pos (inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos)) hsum

/-- Paley–Zygmund for averages: for `Z ≥ 0` and `0 ≤ θ ≤ 1`,
`(1 - θ)² E[Z]² ≤ E[Z²] · Pr[Z > θ E[Z]]`. -/
theorem paley_zygmund {Z : α → ℝ} (hZ : ∀ x, 0 ≤ Z x) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 * average Z ^ 2 ≤
      average (fun x => Z x ^ 2) * average (fun x => if θ * average Z < Z x then 1 else 0) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [average]
  have hm : 0 ≤ average Z := average_nonneg hZ
  have hsplit : ∀ x, Z x ≤ θ * average Z + Z x * (if θ * average Z < Z x then 1 else 0) := by
    intro x
    split_ifs with hx
    · nlinarith [mul_nonneg hθ0 hm]
    · push Not at hx; linarith
  have h1 : (1 - θ) * average Z ≤
      average (fun x => Z x * (if θ * average Z < Z x then 1 else 0)) := by
    have := average_le_average hsplit
    rw [average_add, average_const] at this
    linarith
  have h2 := average_mul_sq_le Z (fun x => if θ * average Z < Z x then (1 : ℝ) else 0)
  rw [average_congr (f := fun x => (if θ * average Z < Z x then (1 : ℝ) else 0) ^ 2)
    (g := fun x => if θ * average Z < Z x then (1 : ℝ) else 0)
    (fun x => by split_ifs <;> norm_num)] at h2
  calc (1 - θ) ^ 2 * average Z ^ 2 = ((1 - θ) * average Z) ^ 2 := by ring
    _ ≤ average (fun x => Z x * (if θ * average Z < Z x then 1 else 0)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by linarith) hm) h1 2
    _ ≤ _ := h2

end Average

variable {ι : Type*} [DecidableEq ι]

/-- The part of `f` not depending on coordinate `i`: `E_i f x = (f x + f (flip i x)) / 2`. -/
def coordAverage (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ := (f x + f (flip i x)) / 2

/-- The coefficient of `x_i` in `f`: `D_i f x = sign (x i) · (f x - f (flip i x)) / 2`. -/
def coordDerivative (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) : ℝ :=
  sign (x i) * derivative i f x

lemma coordAverage_flip (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordAverage i f (flip i x) = coordAverage i f x := by
  simp only [coordAverage, flip_flip]; ring

lemma coordDerivative_flip (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    coordDerivative i f (flip i x) = coordDerivative i f x := by
  simp only [coordDerivative, derivative, flip_flip, flip_apply_self, sign_not]; ring

/-- `f = x_i · D_i f + E_i f`. -/
lemma eq_sign_mul_coordDerivative_add (i : ι) (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = sign (x i) * coordDerivative i f x + coordAverage i f x := by
  simp only [coordDerivative, coordAverage, derivative]
  linear_combination (-(f x - f (flip i x)) / 2) * sign_mul_self (x i)

variable [Fintype ι]

/-- `(E_i f)^ S = f̂ S` for `i ∉ S` and `0` otherwise. -/
lemma fourierCoeff_coordAverage (i : ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (coordAverage i f) S = if i ∈ S then 0 else fourierCoeff f S := by
  have : coordAverage i f = fun x => f x - derivative i f x :=
    funext fun x => by simp only [coordAverage, derivative]; ring
  rw [this, fourierCoeff_sub, fourierCoeff_derivative]
  split_ifs <;> ring

/-- `(D_i f)^ S = f̂ (insert i S)` for `i ∉ S` and `0` otherwise. -/
lemma fourierCoeff_coordDerivative (i : ι) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (coordDerivative i f) S = if i ∈ S then 0 else fourierCoeff f (insert i S) := by
  split_ifs with hiS
  · have key :
        fourierCoeff (coordDerivative i f) S = fourierCoeff (derivative i f) (S.erase i) := by
      simp only [fourierCoeff, coordDerivative, character]
      refine average_congr fun x => ?_
      rw [← mul_prod_erase S (fun j => sign (x j)) hiS]
      linear_combination (derivative i f x * ∏ j ∈ S.erase i, sign (x j)) * sign_mul_self (x i)
    rw [key, fourierCoeff_derivative, ite_eq_right (notMem_erase i S)]
  · have key := fourierCoeff_derivative i f (insert i S)
    rw [ite_eq_left (mem_insert_self i S)] at key
    rw [← key]
    simp only [fourierCoeff, coordDerivative, character]
    refine average_congr fun x => ?_
    rw [prod_insert hiS]
    ring

/-- If `f̂` lives on sets `⊆ insert i T` of size `≤ d + 1`, then `(D_i f)^` lives on sets
`⊆ T` of size `≤ d`. -/
lemma coordDerivative_support {i : ι} {T : Finset ι} {d : ℕ} {f : (ι → Bool) → ℝ}
    (hf : ∀ S, fourierCoeff f S ≠ 0 → S ⊆ insert i T ∧ S.card ≤ d + 1) (S : Finset ι)
    (hS : fourierCoeff (coordDerivative i f) S ≠ 0) : S ⊆ T ∧ S.card ≤ d := by
  rw [fourierCoeff_coordDerivative] at hS
  split_ifs at hS with hiS
  · exact absurd rfl hS
  obtain ⟨hsub, hcard⟩ := hf _ hS
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases mem_insert.1 (hsub (mem_insert_of_mem hx)) with rfl | h
    · exact absurd hx hiS
    · exact h
  · rw [card_insert_of_notMem hiS] at hcard; omega

/-- If `f̂` lives on sets `⊆ insert i T` of size `≤ d`, so does `(E_i f)^` on sets `⊆ T`. -/
lemma coordAverage_support {i : ι} {T : Finset ι} {d : ℕ} {f : (ι → Bool) → ℝ}
    (hf : ∀ S, fourierCoeff f S ≠ 0 → S ⊆ insert i T ∧ S.card ≤ d) (S : Finset ι)
    (hS : fourierCoeff (coordAverage i f) S ≠ 0) : S ⊆ T ∧ S.card ≤ d := by
  rw [fourierCoeff_coordAverage] at hS
  split_ifs at hS with hiS
  · exact absurd rfl hS
  obtain ⟨hsub, hcard⟩ := hf _ hS
  refine ⟨fun x hx => ?_, hcard⟩
  rcases mem_insert.1 (hsub hx) with rfl | h
  · exact absurd hx hiS
  · exact h

/-- `E[x_i · h] = 0` when `h` does not depend on coordinate `i`. -/
lemma average_sign_mul_eq_zero (i : ι) {h : (ι → Bool) → ℝ} (hh : ∀ x, h (flip i x) = h x) :
    average (fun x => sign (x i) * h x) = 0 := by
  have e := average_comp_flip i (fun x => sign (x i) * h x)
  simp only [flip_apply_self, sign_not, hh, neg_mul] at e
  rw [average_neg] at e
  linarith

section Moments

variable {i : ι} {f g e : (ι → Bool) → ℝ} (hf : ∀ x, f x = sign (x i) * g x + e x)
  (hg : ∀ x, g (flip i x) = g x) (he : ∀ x, e (flip i x) = e x)
include hf hg he

/-- `E[f²] = E[g²] + E[e²]` for `f = x_i g + e` with `g, e` independent of `x_i`. -/
lemma average_sq_of_decomp :
    average (fun x => f x ^ 2) = average (fun x => g x ^ 2) + average (fun x => e x ^ 2) := by
  have h0 : average (fun x => sign (x i) * (2 * g x * e x)) = 0 :=
    average_sign_mul_eq_zero i fun x => by simp [hg, he]
  have hpt : ∀ x, f x ^ 2 = (g x ^ 2 + e x ^ 2) + sign (x i) * (2 * g x * e x) := fun x => by
    rw [hf]; linear_combination g x ^ 2 * sign_mul_self (x i)
  rw [average_congr hpt, average_add, average_add, h0, add_zero]

/-- `E[f⁴] = E[g⁴] + 6 E[g² e²] + E[e⁴]` for `f = x_i g + e` as above. -/
lemma average_pow_four_of_decomp :
    average (fun x => f x ^ 4) = average (fun x => g x ^ 4) +
      6 * average (fun x => g x ^ 2 * e x ^ 2) + average (fun x => e x ^ 4) := by
  have h0 : average (fun x => sign (x i) * (4 * g x ^ 3 * e x + 4 * g x * e x ^ 3)) = 0 :=
    average_sign_mul_eq_zero i fun x => by simp [hg, he]
  have hpt : ∀ x, f x ^ 4 = ((g x ^ 4 + 6 * (g x ^ 2 * e x ^ 2)) + e x ^ 4) +
      sign (x i) * (4 * g x ^ 3 * e x + 4 * g x * e x ^ 3) := fun x => by
    rw [hf]
    linear_combination (g x ^ 4 * (sign (x i) ^ 2 + 1) + 6 * g x ^ 2 * e x ^ 2 +
      4 * g x ^ 3 * e x * sign (x i)) * sign_mul_self (x i)
  rw [average_congr hpt, average_add, average_add, average_add, average_const_mul, h0, add_zero]

end Moments

/-- Base case of the Bonami induction: `f` is constant. -/
lemma average_pow_four_le_of_const {f : (ι → Bool) → ℝ} (d : ℕ)
    (hf : ∀ S, fourierCoeff f S ≠ 0 → S = ∅) :
    average (fun x => f x ^ 4) ≤ 9 ^ d * average (fun x => f x ^ 2) ^ 2 := by
  have hc : ∀ x, f x = fourierCoeff f ∅ := fun x => by
    rw [fourier_expansion f x, sum_eq_single ∅]
    · simp
    · intro S _ hS
      by_contra h
      exact hS (hf S (left_ne_zero_of_mul h))
    · simp
  simp only [hc, average_const]
  have h9 : (1 : ℝ) ≤ 9 ^ d := one_le_pow₀ (by norm_num)
  nlinarith [mul_le_mul_of_nonneg_right h9 (pow_nonneg (sq_nonneg (fourierCoeff f ∅)) 2)]

/-- Induction step of the Bonami lemma. -/
lemma bonami_step {i : ι} {f g e : (ι → Bool) → ℝ} (k : ℕ)
    (hf : ∀ x, f x = sign (x i) * g x + e x)
    (hg : ∀ x, g (flip i x) = g x) (he : ∀ x, e (flip i x) = e x)
    (hg4 : average (fun x => g x ^ 4) ≤ 9 ^ k * average (fun x => g x ^ 2) ^ 2)
    (he4 : average (fun x => e x ^ 4) ≤ 9 ^ (k + 1) * average (fun x => e x ^ 2) ^ 2) :
    average (fun x => f x ^ 4) ≤ 9 ^ (k + 1) * average (fun x => f x ^ 2) ^ 2 := by
  rw [average_pow_four_of_decomp hf hg he, average_sq_of_decomp hf hg he]
  have hX2 : average (fun x => g x ^ 2 * e x ^ 2) ^ 2 ≤
      average (fun x => g x ^ 4) * average (fun x => e x ^ 4) := by
    have h := average_mul_sq_le (fun x => g x ^ 2) (fun x => e x ^ 2)
    rwa [average_congr (f := fun x => (g x ^ 2) ^ 2) (g := fun x => g x ^ 4)
      (fun x => by ring), average_congr (f := fun x => (e x ^ 2) ^ 2) (g := fun x => e x ^ 4)
      (fun x => by ring)] at h
  have hX0 : 0 ≤ average (fun x => g x ^ 2 * e x ^ 2) :=
    average_nonneg fun x => by positivity
  have hg40 : 0 ≤ average (fun x => g x ^ 4) := average_nonneg fun x => by positivity
  set A := average (fun x => e x ^ 2) with hA
  set B := average (fun x => g x ^ 2) with hB
  set X := average (fun x => g x ^ 2 * e x ^ 2) with hXdef
  have hA0 : 0 ≤ A := average_nonneg fun x => sq_nonneg (e x)
  have hB0 : 0 ≤ B := average_nonneg fun x => sq_nonneg (g x)
  have hN : (0 : ℝ) ≤ 9 ^ k := by positivity
  rw [pow_succ 9 k] at he4 ⊢
  have hX : X ≤ 3 * 9 ^ k * B * A := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    calc X ^ 2 ≤ average (fun x => g x ^ 4) * average (fun x => e x ^ 4) := hX2
      _ ≤ (9 ^ k * B ^ 2) * (9 ^ k * 9 * A ^ 2) :=
          mul_le_mul hg4 he4 (average_nonneg fun x => by positivity) (by positivity)
      _ = (3 * 9 ^ k * B * A) ^ 2 := by ring
  nlinarith [mul_nonneg hN (sq_nonneg B)]

/-- The Bonami lemma relative to a coordinate set: if every nonzero `f̂ S` has `S ⊆ T` and
`|S| ≤ d`, then `E[f⁴] ≤ 9^d E[f²]²`. -/
theorem bonami_of_support (T : Finset ι) {d : ℕ} {f : (ι → Bool) → ℝ}
    (hf : ∀ S, fourierCoeff f S ≠ 0 → S ⊆ T ∧ S.card ≤ d) :
    average (fun x => f x ^ 4) ≤ 9 ^ d * average (fun x => f x ^ 2) ^ 2 := by
  induction T using Finset.induction_on generalizing d f with
  | empty =>
    exact average_pow_four_le_of_const d fun S hS => subset_empty.1 (hf S hS).1
  | @insert j T _ ih =>
    rcases d with _ | k
    · exact average_pow_four_le_of_const 0 fun S hS =>
        card_eq_zero.1 (Nat.le_zero.1 (hf S hS).2)
    · exact bonami_step k (eq_sign_mul_coordDerivative_add j f) (coordDerivative_flip j f)
        (coordAverage_flip j f)
        (ih (d := k) (f := coordDerivative j f) (coordDerivative_support hf))
        (ih (d := k + 1) (f := coordAverage j f) (coordAverage_support hf))

/-- **Bonami lemma**: `E[f⁴] ≤ 9^d E[f²]²` for `f` of Fourier degree at most `d`. -/
theorem bonami {d : ℕ} {f : (ι → Bool) → ℝ} (hf : degree f ≤ d) :
    average (fun x => f x ^ 4) ≤ 9 ^ d * average (fun x => f x ^ 2) ^ 2 :=
  bonami_of_support univ fun S hS => ⟨subset_univ S, (card_le_degree hS).trans hf⟩

/-- `E[f²] ≤ 9^d E[|f|]²` for `f` of degree at most `d` (from Bonami and Cauchy–Schwarz). -/
theorem average_sq_le_of_degree_le {d : ℕ} {f : (ι → Bool) → ℝ} (hf : degree f ≤ d) :
    average (fun x => f x ^ 2) ≤ 9 ^ d * average (fun x => |f x|) ^ 2 := by
  have h4 := bonami hf
  have h1 : average (fun x => f x ^ 2) ^ 2 ≤
      average (fun x => |f x|) * average (fun x => |f x| * f x ^ 2) :=
    average_sq_le_mul (r := fun x => f x ^ 2) (u := fun x => |f x|)
      (v := fun x => |f x| * f x ^ 2) (fun x => abs_nonneg _)
      (fun x => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun x => by
        show (f x ^ 2) ^ 2 ≤ |f x| * (|f x| * f x ^ 2)
        rw [← mul_assoc, abs_mul_abs_self]; exact le_of_eq (by ring))
  have h2 := average_mul_sq_le (fun x => |f x|) (fun x => f x ^ 2)
  rw [average_congr (f := fun x => |f x| ^ 2) (g := fun x => f x ^ 2) (fun x => sq_abs _),
    average_congr (f := fun x => (f x ^ 2) ^ 2) (g := fun x => f x ^ 4) (fun x => by ring)] at h2
  set a := average (fun x => |f x|) with ha
  set b := average (fun x => f x ^ 2) with hb
  set c := average (fun x => |f x| * f x ^ 2) with hc
  set E := average (fun x => f x ^ 4) with hE
  have ha0 : 0 ≤ a := average_nonneg fun x => abs_nonneg _
  have hb0 : 0 ≤ b := average_nonneg fun x => sq_nonneg _
  rcases hb0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  have key : b ^ 3 * b ≤ b ^ 3 * (9 ^ d * a ^ 2) := by
    have hb4 : (b ^ 2) ^ 2 ≤ (a * c) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    calc b ^ 3 * b = (b ^ 2) ^ 2 := by ring
      _ ≤ (a * c) ^ 2 := hb4
      _ = a ^ 2 * c ^ 2 := by ring
      _ ≤ a ^ 2 * (b * E) := by gcongr
      _ ≤ a ^ 2 * (b * (9 ^ d * b ^ 2)) := by gcongr
      _ = b ^ 3 * (9 ^ d * a ^ 2) := by ring
  exact le_of_mul_le_mul_left key (pow_pos hpos 3)

/-- Anti-concentration: for `f ≠ 0` of degree at most `d` and `0 ≤ θ ≤ 1`,
`Pr[f² > θ E[f²]] ≥ (1 - θ)² / 9^d`. -/
theorem anticoncentration_of_degree_le {d : ℕ} {f : (ι → Bool) → ℝ} (hf : degree f ≤ d)
    (hne : ∃ x, f x ≠ 0) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ) ^ 2 / 9 ^ d ≤
      average (fun x => if θ * average (fun y => f y ^ 2) < f x ^ 2 then 1 else 0) := by
  have hpz := paley_zygmund (Z := fun x => f x ^ 2) (fun x => sq_nonneg (f x)) hθ0 hθ1
  have h4 := bonami hf
  have hb := average_sq_pos hne
  rw [average_congr (f := fun x => (f x ^ 2) ^ 2) (g := fun x => f x ^ 4) (fun x => by ring)]
    at hpz
  have hP0 : 0 ≤ average (fun x => if θ * average (fun y => f y ^ 2) < f x ^ 2 then 1 else 0) :=
    average_nonneg fun x => by split_ifs <;> norm_num
  set b := average (fun x => f x ^ 2) with hbdef
  set P := average (fun x => if θ * b < f x ^ 2 then (1 : ℝ) else 0) with hPdef
  have key : (1 - θ) ^ 2 * b ^ 2 ≤ (P * 9 ^ d) * b ^ 2 :=
    calc (1 - θ) ^ 2 * b ^ 2 ≤ average (fun x => f x ^ 4) * P := hpz
      _ ≤ (9 ^ d * b ^ 2) * P := mul_le_mul_of_nonneg_right h4 hP0
      _ = (P * 9 ^ d) * b ^ 2 := by ring
  rw [div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right key (pow_pos hb 2)

/-- A nonzero mean-zero `f` of degree at most `d` is positive with probability at least
`1 / (4 · 9^d)`. -/
theorem prob_pos_ge_of_degree_le {d : ℕ} {f : (ι → Bool) → ℝ} (hf : degree f ≤ d)
    (hmean : average f = 0) (hne : ∃ x, f x ≠ 0) :
    1 / (4 * 9 ^ d) ≤ average (fun x => if 0 < f x then 1 else 0) := by
  have hhalf : average (fun x => f x * (if 0 < f x then 1 else 0)) =
      average (fun x => |f x|) / 2 := by
    have hpt : ∀ x, f x * (if 0 < f x then 1 else 0) = 1 / 2 * |f x| + 1 / 2 * f x := by
      intro x
      split_ifs with hx
      · rw [abs_of_pos hx]; ring
      · rw [abs_of_nonpos (not_lt.1 hx)]; ring
    rw [average_congr hpt, average_add, average_const_mul, average_const_mul]
    linarith [hmean]
  have hcs := average_mul_sq_le f (fun x => if 0 < f x then (1 : ℝ) else 0)
  rw [average_congr (f := fun x => (if 0 < f x then (1 : ℝ) else 0) ^ 2)
    (g := fun x => if 0 < f x then (1 : ℝ) else 0) (fun x => by split_ifs <;> norm_num),
    hhalf] at hcs
  have hl2 := average_sq_le_of_degree_le hf
  have hb := average_sq_pos hne
  have hP0 : 0 ≤ average (fun x => if 0 < f x then (1 : ℝ) else 0) :=
    average_nonneg fun x => by split_ifs <;> norm_num
  set a := average (fun x => |f x|) with ha
  set b := average (fun x => f x ^ 2) with hbdef
  set P := average (fun x => if 0 < f x then (1 : ℝ) else 0) with hPdef
  have key : 1 * b ≤ (P * (4 * 9 ^ d)) * b := by
    calc 1 * b = b := one_mul b
      _ ≤ 9 ^ d * a ^ 2 := hl2
      _ = 9 ^ d * 4 * (a / 2) ^ 2 := by ring
      _ ≤ 9 ^ d * 4 * (b * P) := by gcongr
      _ = (P * (4 * 9 ^ d)) * b := by ring
  rw [div_le_iff₀ (by positivity)]
  exact le_of_mul_le_mul_right key hb






end

end TheoremOS.BooleanCube
