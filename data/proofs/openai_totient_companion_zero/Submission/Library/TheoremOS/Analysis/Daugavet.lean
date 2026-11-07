import Mathlib

/-!
# The Daugavet property and the slice lemma

A real normed space `X` has the Daugavet property (`HasDaugavetProperty X`) when every rank-one
operator `T = ℓ.smulRight v` satisfies `‖Id + T‖ = 1 + ‖T‖`. The slice lemma of Kadets, Shvidkoy,
Sirotkin and Werner: in such a space, every nonempty slice `{y | ‖y‖ ≤ 1, α < ℓ y}` of the unit
ball contains, for every unit vector `w` and every `ρ > 0`, a unit vector `y` with
`‖w + y‖ ≥ 2 - ρ` (`HasDaugavetProperty.unitSlice`). Along the way: a vector `z` of the unit ball
with `‖z + ℓ z • w‖ > 2 - δ` and `ℓ z ≥ 0` normalises to a unit vector `u` with `ℓ u > 1 - δ` and
`‖u + w‖ > 2 - 3δ` (`exists_unit_of_norm_add_smul_gt`).

Sources: V. M. Kadets, R. V. Shvidkoy, G. G. Sirotkin and D. Werner, *Banach spaces with the
Daugavet property*, Trans. Amer. Math. Soc. 352 (2000) 855–873, §2 (the slice
characterisation, proved here in the direction used: Daugavet equation ⇒ slices); D. Werner,
*Recent progress on the Daugavet property*, Irish Math. Soc. Bull. 46 (2001).
Classical material; nothing here is specific to a benchmark problem.

Bridges: `StrongDual ℝ X` is `X →L[ℝ] ℝ`, and `ContinuousLinearMap.id ℝ X + ell.smulRight v`
applied to `x` is `x + ell x • v` (`ContinuousLinearMap.smulRight_apply`); a definition
`∀ (ell : X →L[ℝ] ℝ) (v : X), ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ =
1 + ‖ell.smulRight v‖` is `HasDaugavetProperty X` by `Iff.rfl`, and the slice condition
`∀ w, ‖w‖ = 1 → ∀ ell α, (∃ u, ‖u‖ ≤ 1 ∧ α < ell u) → ∀ ρ, 0 < ρ → ∃ y, ‖y‖ = 1 ∧ α < ell y ∧
2 - ρ ≤ ‖w + y‖` is `HasUnitSliceProperty X`. `‖ell.smulRight v‖ = ‖ell‖ * ‖v‖` is Mathlib's
`ContinuousLinearMap.norm_smulRight_apply`.
-/

namespace TheoremOS.Analysis

noncomputable section

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Daugavet equation `‖Id + T‖ = 1 + ‖T‖` for every rank-one operator `T`. -/
def HasDaugavetProperty : Prop :=
  ∀ (ell : X →L[ℝ] ℝ) (v : X),
    ‖ContinuousLinearMap.id ℝ X + ell.smulRight v‖ = 1 + ‖ell.smulRight v‖

/-- Every nonempty slice of the unit ball contains unit vectors almost antipodal to `-w`. -/
def HasUnitSliceProperty : Prop :=
  ∀ w : X, ‖w‖ = 1 → ∀ (ell : X →L[ℝ] ℝ) (α : ℝ), (∃ u : X, ‖u‖ ≤ 1 ∧ α < ell u) →
    ∀ ρ : ℝ, 0 < ρ → ∃ y : X, ‖y‖ = 1 ∧ α < ell y ∧ 2 - ρ ≤ ‖w + y‖

variable {X}

/-- Normalisation step of the slice lemma. -/
theorem exists_unit_of_norm_add_smul_gt {ell : X →L[ℝ] ℝ} (hell : ‖ell‖ = 1) {w z : X}
    (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) (hz0 : 0 ≤ ell z) {δ : ℝ} (hδ : δ < 1)
    (h : 2 - δ < ‖z + ell z • w‖) :
    ∃ u : X, ‖u‖ = 1 ∧ 1 - δ < ell u ∧ 2 - 3 * δ < ‖u + w‖ := by
  have hle : ell z ≤ ‖z‖ := by
    have := ell.le_opNorm z
    rw [hell, one_mul] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have htri : ‖z + ell z • w‖ ≤ ‖z‖ + ell z := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg hz0]
  have hlz : 1 - δ < ell z := by linarith
  have hnz : 1 - δ < ‖z‖ := by linarith
  have hzw : 2 - 2 * δ < ‖z + w‖ := by
    have e : z + ell z • w = (z + w) - (1 - ell z) • w := by
      rw [sub_smul, one_smul]; abel
    have : ‖z + ell z • w‖ ≤ ‖z + w‖ + (1 - ell z) := by
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  refine ⟨‖z‖⁻¹ • z, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzpos.ne']
  · rw [map_smul, smul_eq_mul]
    have : 1 ≤ ‖z‖⁻¹ := (one_le_inv₀ hzpos).mpr hz
    nlinarith
  · have hd : ‖‖z‖⁻¹ • z - z‖ = 1 - ‖z‖ := by
      rw [show ‖z‖⁻¹ • z - z = (‖z‖⁻¹ - 1) • z by rw [sub_smul, one_smul], norm_smul,
        Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ((one_le_inv₀ hzpos).mpr hz)), sub_mul,
        inv_mul_cancel₀ hzpos.ne', one_mul]
    have : ‖z + w‖ ≤ ‖‖z‖⁻¹ • z + w‖ + ‖‖z‖⁻¹ • z - z‖ := by
      calc ‖z + w‖ = ‖(‖z‖⁻¹ • z + w) - (‖z‖⁻¹ • z - z)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith

/-- **Slice lemma** (Kadets–Shvidkoy–Sirotkin–Werner). -/
theorem HasDaugavetProperty.unitSlice (hX : HasDaugavetProperty X) : HasUnitSliceProperty X := by
  intro w hw ell α hslice ρ hρ
  obtain ⟨u₀, hu₀, hαu₀⟩ := hslice
  by_cases hell : ell = 0
  · subst hell
    refine ⟨w, hw, by simpa using hαu₀, ?_⟩
    rw [← two_smul ℝ w, norm_smul, hw]
    norm_num
    linarith
  have hn : 0 < ‖ell‖ := norm_pos_iff.mpr hell
  set ell' : X →L[ℝ] ℝ := ‖ell‖⁻¹ • ell with hell'
  have hn' : ‖ell'‖ = 1 := by
    rw [hell', norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hα : α / ‖ell‖ < 1 := by
    rw [div_lt_one hn]
    calc α < ell u₀ := hαu₀
      _ ≤ ‖ell u₀‖ := le_abs_self _
      _ ≤ ‖ell‖ * ‖u₀‖ := ell.le_opNorm u₀
      _ ≤ ‖ell‖ := by nlinarith [norm_nonneg u₀]
  set δ := min (min (ρ / 3) (1 - α / ‖ell‖)) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hδρ : δ ≤ ρ / 3 := (min_le_left _ _).trans (min_le_left _ _)
  have hδα : δ ≤ 1 - α / ‖ell‖ := (min_le_left _ _).trans (min_le_right _ _)
  have hnorm : ‖ContinuousLinearMap.id ℝ X + ell'.smulRight w‖ = 2 := by
    rw [hX, ContinuousLinearMap.norm_smulRight_apply, hn', hw]; norm_num
  obtain ⟨z, hz, hzgt⟩ := (ContinuousLinearMap.id ℝ X + ell'.smulRight w).exists_lt_apply_of_lt_opNorm
    (r := 2 - δ) (by rw [hnorm]; linarith)
  have happ : ∀ x : X, (ContinuousLinearMap.id ℝ X + ell'.smulRight w) x = x + ell' x • w :=
    fun _ => rfl
  rw [happ] at hzgt
  obtain ⟨z', hz', hz'0, hz'gt⟩ : ∃ z' : X, ‖z'‖ ≤ 1 ∧ 0 ≤ ell' z' ∧ 2 - δ < ‖z' + ell' z' • w‖ := by
    rcases le_total 0 (ell' z) with h0 | h0
    · exact ⟨z, hz.le, h0, hzgt⟩
    · refine ⟨-z, by rw [norm_neg]; exact hz.le, by rw [map_neg]; linarith, ?_⟩
      rw [map_neg, neg_smul, ← neg_add, norm_neg]
      exact hzgt
  obtain ⟨u, hu, hlu, hwu⟩ := exists_unit_of_norm_add_smul_gt hn' hw hz' hz'0 hδ1 hz'gt
  refine ⟨u, hu, ?_, ?_⟩
  · have h1 : α / ‖ell‖ < ell' u := lt_of_le_of_lt (by linarith) hlu
    have e : ell' u = ‖ell‖⁻¹ * ell u := rfl
    rw [e, div_eq_inv_mul] at h1
    exact lt_of_mul_lt_mul_left h1 (inv_nonneg.mpr hn.le)
  · rw [add_comm]
    linarith

end

end TheoremOS.Analysis
