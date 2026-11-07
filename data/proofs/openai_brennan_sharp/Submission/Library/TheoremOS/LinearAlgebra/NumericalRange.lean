import Mathlib

/-!
# The numerical range of an operator on a complex inner product space

For `T : E →L[ℂ] E`, `numericalRange T = {⟪x, T x⟫ | ‖x‖ = 1}` and
`numericalRadius T = sSup ‖numericalRange T‖`. This file proves: Rayleigh quotients
`⟪x, T x⟫ / ‖x‖²` of nonzero vectors lie in the range; it is nonempty on a nontrivial space and
lies in the closed ball of radius `‖T‖`; eigenvalues lie in it; affine maps act on it,
`W(a • T + b • 1) = (a · + b) '' W(T)`; `W(T†) = conj '' W(T)`; self-adjoint operators have real
numerical range; compressions by isometries shrink it and linear isometric equivalences preserve
it; it is compact in finite dimension; the Toeplitz–Hausdorff theorem (convexity); and
`numericalRadius T ≤ ‖T‖ ≤ 2 · numericalRadius T`.

Sources: O. Toeplitz, *Das algebraische Analogon zu einem Satze von Fejér*, Math. Z. 2 (1918);
F. Hausdorff, *Der Wertvorrat einer Bilinearform*, Math. Z. 3 (1919); K. E. Gustafson and
D. K. M. Rao, *Numerical Range: The Field of Values of Linear Operators and Matrices*, Springer,
1997, Chapter 1 (Toeplitz–Hausdorff via the two-dimensional reduction, the bounds
`w(T) ≤ ‖T‖ ≤ 2 w(T)`); R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge
University Press, 1991, Chapter 1 (the field of values, its elementary properties). Textbook
material; nothing here is specific to a benchmark problem.

Bridges: `numericalRange T` unfolds to `{z | ∃ x, ‖x‖ = 1 ∧ ⟪x, T x⟫_ℂ = z}`, and
`⟪x, y⟫_ℂ` is `inner ℂ x y`, so a set `{z | ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖ = 1 ∧
inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u) = z}` is
`numericalRange (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A)` by `rfl`. With
`open scoped Matrix.Norms.L2Operator`, `‖Matrix.toEuclideanCLM A‖ = ‖A‖` is
`Matrix.l2_opNorm_toEuclideanCLM` (`rfl`). The convention is Mathlib's: the inner product is
conjugate-linear in the first argument.
-/

namespace TheoremOS.LinearAlgebra

open Set Metric ComplexConjugate
open scoped InnerProductSpace

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The numerical range (field of values) `{⟪x, T x⟫ | ‖x‖ = 1}`. -/
def numericalRange (T : E →L[ℂ] E) : Set ℂ := {z | ∃ x : E, ‖x‖ = 1 ∧ ⟪x, T x⟫_ℂ = z}

/-- The numerical radius `sup {‖z‖ | z ∈ W(T)}` (`0` on the zero space). -/
def numericalRadius (T : E →L[ℂ] E) : ℝ := sSup ((fun z => ‖z‖) '' numericalRange T)

lemma mem_numericalRange {T : E →L[ℂ] E} {z : ℂ} :
    z ∈ numericalRange T ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, T x⟫_ℂ = z := Iff.rfl

lemma inner_map_self_mem_numericalRange (T : E →L[ℂ] E) {x : E} (hx : ‖x‖ = 1) :
    ⟪x, T x⟫_ℂ ∈ numericalRange T := ⟨x, hx, rfl⟩

lemma inner_smul_map_smul (T : E →L[ℂ] E) (c : ℂ) (x : E) :
    ⟪c • x, T (c • x)⟫_ℂ = ((‖c‖ ^ 2 : ℝ) : ℂ) * ⟪x, T x⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul']
  push_cast; ring

/-- Rayleigh quotients of nonzero vectors lie in the numerical range. -/
theorem div_norm_sq_mem_numericalRange (T : E →L[ℂ] E) {x : E} (hx : x ≠ 0) :
    ⟪x, T x⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ) ∈ numericalRange T := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  refine ⟨((‖x‖⁻¹ : ℝ) : ℂ) • x, ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  · rw [inner_smul_map_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, div_eq_inv_mul]
    congr 1
    push_cast
    rw [inv_pow]

theorem numericalRange_nonempty [Nontrivial E] (T : E →L[ℂ] E) : (numericalRange T).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  exact ⟨_, div_norm_sq_mem_numericalRange T hx⟩

theorem norm_le_of_mem_numericalRange {T : E →L[ℂ] E} {z : ℂ} (hz : z ∈ numericalRange T) :
    ‖z‖ ≤ ‖T‖ := by
  obtain ⟨x, hx, rfl⟩ := hz
  calc ‖⟪x, T x⟫_ℂ‖ ≤ ‖x‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm x
    _ = ‖T‖ := by rw [hx]; ring

theorem numericalRange_subset_closedBall (T : E →L[ℂ] E) :
    numericalRange T ⊆ closedBall 0 ‖T‖ := fun _ hz => by
  rw [mem_closedBall, dist_zero_right]
  exact norm_le_of_mem_numericalRange hz

theorem isBounded_numericalRange (T : E →L[ℂ] E) : Bornology.IsBounded (numericalRange T) :=
  isBounded_closedBall.subset (numericalRange_subset_closedBall T)

/-- Eigenvalues lie in the numerical range. -/
theorem mem_numericalRange_of_eigenvector {T : E →L[ℂ] E} {μ : ℂ} {x : E} (hx : x ≠ 0)
    (hTx : T x = μ • x) : μ ∈ numericalRange T := by
  have hn : ((‖x‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have := norm_ne_zero_iff.mpr hx
    exact_mod_cast pow_ne_zero 2 this
  have h := div_norm_sq_mem_numericalRange T hx
  have e : ⟪x, T x⟫_ℂ / ((‖x‖ ^ 2 : ℝ) : ℂ) = μ := by
    rw [hTx, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_eq_complex_ofReal,
      ← RCLike.ofReal_pow, mul_div_assoc]
    change μ * (((‖x‖ ^ 2 : ℝ) : ℂ) / ((‖x‖ ^ 2 : ℝ) : ℂ)) = μ
    rw [div_self hn, mul_one]
  rwa [e] at h

theorem mem_numericalRange_of_hasEigenvalue {T : E →L[ℂ] E} {μ : ℂ}
    (h : Module.End.HasEigenvalue (T : E →ₗ[ℂ] E) μ) : μ ∈ numericalRange T := by
  obtain ⟨x, hx⟩ := h.exists_hasEigenvector
  exact mem_numericalRange_of_eigenvector hx.2 (Module.End.mem_eigenspace_iff.mp hx.1)

/-- In finite dimension the spectrum of the underlying linear map lies in the numerical range. -/
theorem spectrum_subset_numericalRange [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    spectrum ℂ (T : E →ₗ[ℂ] E) ⊆ numericalRange T := fun _ hμ =>
  mem_numericalRange_of_hasEigenvalue (Module.End.hasEigenvalue_iff_mem_spectrum.mpr hμ)

section Transformations

lemma inner_map_self_affine (T : E →L[ℂ] E) (a b : ℂ) {x : E} (hx : ‖x‖ = 1) :
    ⟪x, (a • T + b • (1 : E →L[ℂ] E)) x⟫_ℂ = a * ⟪x, T x⟫_ℂ + b := by
  change ⟪x, a • T x + b • x⟫_ℂ = _
  rw [inner_add_right, inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hx]
  simp

/-- Affine maps act on the numerical range: `W(a • T + b • 1) = (a · + b) '' W(T)`. -/
theorem numericalRange_affine (T : E →L[ℂ] E) (a b : ℂ) :
    numericalRange (a • T + b • (1 : E →L[ℂ] E)) = (fun z => a * z + b) '' numericalRange T := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (inner_map_self_affine T a b hx).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, inner_map_self_affine T a b hx⟩

theorem numericalRange_smul (T : E →L[ℂ] E) (a : ℂ) :
    numericalRange (a • T) = (fun z => a * z) '' numericalRange T := by
  simpa using numericalRange_affine T a 0

theorem numericalRange_add_smul_one (T : E →L[ℂ] E) (b : ℂ) :
    numericalRange (T + b • (1 : E →L[ℂ] E)) = (fun z => z + b) '' numericalRange T := by
  simpa using numericalRange_affine T 1 b

/-- Compression by an isometry shrinks the numerical range: if `V : F → E` is isometric and
`⟪y, S y⟫ = ⟪V y, T (V y)⟫`, then `W(S) ⊆ W(T)`. -/
theorem numericalRange_subset_of_isometry {S : F →L[ℂ] F} {T : E →L[ℂ] E} (V : F →ₗᵢ[ℂ] E)
    (h : ∀ y, ⟪y, S y⟫_ℂ = ⟪V y, T (V y)⟫_ℂ) : numericalRange S ⊆ numericalRange T := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨V y, by rw [V.norm_map, hy], (h y).symm⟩

/-- Operators intertwined by a linear isometric equivalence, `S ∘ U = U ∘ T`, have the same
numerical range. -/
theorem numericalRange_eq_of_linearIsometryEquiv {S : F →L[ℂ] F} {T : E →L[ℂ] E} (U : E ≃ₗᵢ[ℂ] F)
    (h : ∀ x, S (U x) = U (T x)) : numericalRange S = numericalRange T := by
  apply Subset.antisymm
  · refine numericalRange_subset_of_isometry U.symm.toLinearIsometry fun y => ?_
    have := h (U.symm y)
    rw [U.apply_symm_apply] at this
    rw [LinearIsometryEquiv.coe_toLinearIsometry, ← U.inner_map_map, U.apply_symm_apply, this]
  · refine numericalRange_subset_of_isometry U.toLinearIsometry fun x => ?_
    rw [LinearIsometryEquiv.coe_toLinearIsometry, h, U.inner_map_map]

/-- Unitary conjugation preserves the numerical range. -/
theorem numericalRange_unitary_conj [CompleteSpace E] (T : E →L[ℂ] E) (u : unitary (E →L[ℂ] E)) :
    numericalRange ((u : E →L[ℂ] E) * T * star (u : E →L[ℂ] E)) = numericalRange T := by
  refine numericalRange_eq_of_linearIsometryEquiv (Unitary.linearIsometryEquiv u) fun x => ?_
  change (u : E →L[ℂ] E) (T ((star (u : E →L[ℂ] E)) ((u : E →L[ℂ] E) x))) = (u : E →L[ℂ] E) (T x)
  have h1 : (star (u : E →L[ℂ] E)) ((u : E →L[ℂ] E) x) = x :=
    congrArg (fun f : E →L[ℂ] E => f x) (Unitary.star_mul_self_of_mem u.prop)
  rw [h1]

end Transformations

section Adjoint

variable [CompleteSpace E]

lemma inner_map_self_adjoint (T : E →L[ℂ] E) (x : E) :
    ⟪x, (ContinuousLinearMap.adjoint T) x⟫_ℂ = conj ⟪x, T x⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- `W(T†) = conj '' W(T)`. -/
theorem numericalRange_adjoint (T : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint T) = conj '' numericalRange T := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (inner_map_self_adjoint T x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, inner_map_self_adjoint T x⟩

theorem numericalRange_star (T : E →L[ℂ] E) : numericalRange (star T) = conj '' numericalRange T := by
  rw [ContinuousLinearMap.star_eq_adjoint, numericalRange_adjoint]

/-- Self-adjoint operators have real numerical range. -/
theorem im_eq_zero_of_mem_numericalRange {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {z : ℂ}
    (hz : z ∈ numericalRange T) : z.im = 0 := by
  obtain ⟨x, -, rfl⟩ := hz
  exact hT.isSymmetric.im_inner_self_apply x

end Adjoint

theorem isCompact_numericalRange [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    IsCompact (numericalRange T) := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have h : numericalRange T = (fun x => ⟪x, T x⟫_ℂ) '' sphere (0 : E) 1 := by
    ext z; simp [numericalRange]
  rw [h]
  exact (isCompact_sphere 0 1).image (continuous_id.inner T.continuous)

theorem isClosed_numericalRange [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    IsClosed (numericalRange T) :=
  (isCompact_numericalRange T).isClosed

section Convex

/-- The two-dimensional step of Toeplitz–Hausdorff: if `⟪x, S x⟫ = 0` and `⟪y, S y⟫ = 1` for unit
vectors `x`, `y`, then every `t ∈ [0, 1]` lies in `W(S)`. -/
theorem ofReal_mem_numericalRange_of_zero_one {S : E →L[ℂ] E} {x y : E} (hx : ‖x‖ = 1)
    (hy : ‖y‖ = 1) (hx0 : ⟪x, S x⟫_ℂ = 0) (hy1 : ⟪y, S y⟫_ℂ = 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) ∈ numericalRange S := by
  -- Rotate `y` so that the cross term `⟪x, S w⟫ + ⟪w, S x⟫` is real.
  set R : ℂ := ⟪x, S y⟫_ℂ - conj ⟪y, S x⟫_ℂ with hR
  obtain ⟨ω, hω, hωR⟩ : ∃ ω : ℂ, ‖ω‖ = 1 ∧ (ω * R).im = 0 := by
    by_cases h0 : R = 0
    · exact ⟨1, by simp, by simp [h0]⟩
    · refine ⟨conj R / ((‖R‖ : ℝ) : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          div_self (norm_ne_zero_iff.mpr h0)]
      · rw [div_mul_eq_mul_div, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_div,
          Complex.ofReal_im]
  set w : E := ω • y with hw
  have hw1 : ‖w‖ = 1 := by rw [hw, norm_smul, hω, hy, one_mul]
  have hwS : ⟪w, S w⟫_ℂ = 1 := by
    rw [hw, inner_smul_map_smul, hω, hy1]; simp
  set c : ℂ := ⟪x, S w⟫_ℂ + ⟪w, S x⟫_ℂ with hc
  have hcim : c.im = 0 := by
    have e : c = ω * ⟪x, S y⟫_ℂ + conj ω * ⟪y, S x⟫_ℂ := by
      rw [hc, hw, map_smul, inner_smul_right, inner_smul_left]
    have hRim := hωR
    rw [hR] at hRim
    rw [e]
    simp only [Complex.mul_im, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.sub_im,
      Complex.sub_re] at hRim ⊢
    linear_combination hRim
  -- The path `v s = (1 - s) x + s w` and its quadratic form.
  let v : ℝ → E := fun s => ((1 - s : ℝ) : ℂ) • x + ((s : ℝ) : ℂ) • w
  have hq : ∀ s : ℝ, ⟪v s, S (v s)⟫_ℂ = ((s ^ 2 : ℝ) : ℂ) + (((1 - s) * s : ℝ) : ℂ) * c := by
    intro s
    simp only [v, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, hx0, hwS, hc]
    push_cast; ring
  have hv0 : ∀ s : ℝ, v s ≠ 0 := by
    intro s hs
    have h1 : ((1 - s : ℝ) : ℂ) • x = ((-s : ℝ) : ℂ) • w := by
      rw [Complex.ofReal_neg, neg_smul, ← sub_eq_zero, sub_neg_eq_add]
      exact hs
    have h2 := congrArg (fun z => ⟪z, S z⟫_ℂ) h1
    simp only [inner_smul_map_smul, hx0, hwS, mul_zero, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs] at h2
    have hs0 : s = 0 := by
      have : (-s) ^ 2 = 0 := by exact_mod_cast h2.symm
      nlinarith
    subst hs0
    have hx' : x ≠ 0 := fun h => by simp [h] at hx
    exact hx' (by simpa [v] using hs)
  have hcont_v : Continuous v := by
    apply Continuous.add
    · exact (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).smul continuous_const
    · exact (Complex.continuous_ofReal.comp continuous_id).smul continuous_const
  let f : ℝ → ℝ := fun s => (⟪v s, S (v s)⟫_ℂ).re / ‖v s‖ ^ 2
  have hf : ContinuousOn f (Icc 0 1) := by
    refine (Continuous.continuousOn ?_).div (Continuous.continuousOn ?_) fun s _ => ?_
    · exact Complex.continuous_re.comp (hcont_v.inner (S.continuous.comp hcont_v))
    · exact (continuous_norm.comp hcont_v).pow 2
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hv0 s))
  have hf0 : f 0 = 0 := by simp [f, v, hx0]
  have hf1 : f 1 = 1 := by simp [f, v, hwS, hw1]
  obtain ⟨s, -, hs⟩ : ∃ s ∈ Icc (0 : ℝ) 1, f s = t := by
    have := intermediate_value_Icc (zero_le_one' ℝ) hf
    rw [hf0, hf1] at this
    exact this ht
  have hreal : ⟪v s, S (v s)⟫_ℂ = (((⟪v s, S (v s)⟫_ℂ).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, hq, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_im,
        Complex.ofReal_re, hcim]
      ring
  have hmem := div_norm_sq_mem_numericalRange S (hv0 s)
  have ht' : (t : ℂ) = ⟪v s, S (v s)⟫_ℂ / ((‖v s‖ ^ 2 : ℝ) : ℂ) := by
    rw [hreal, ← Complex.ofReal_div, ← hs]
  rwa [ht']

/-- **Toeplitz–Hausdorff**: the numerical range is convex. -/
theorem convex_numericalRange (T : E →L[ℂ] E) : Convex ℝ (numericalRange T) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
  by_cases hxy : ⟪x, T x⟫_ℂ = ⟪y, T y⟫_ℂ
  · rw [hxy, ← add_smul, hab, one_smul]
    exact ⟨y, hy, rfl⟩
  set d : ℂ := ⟪y, T y⟫_ℂ - ⟪x, T x⟫_ℂ with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  set S : E →L[ℂ] E := d⁻¹ • T + (-(d⁻¹ * ⟪x, T x⟫_ℂ)) • (1 : E →L[ℂ] E) with hS
  have hSu : ∀ u : E, ‖u‖ = 1 → ⟪u, S u⟫_ℂ = d⁻¹ * (⟪u, T u⟫_ℂ - ⟪x, T x⟫_ℂ) := by
    intro u hu
    rw [hS, inner_map_self_affine T _ _ hu]
    ring
  have hSx : ⟪x, S x⟫_ℂ = 0 := by rw [hSu x hx, sub_self, mul_zero]
  have hSy : ⟪y, S y⟫_ℂ = 1 := by rw [hSu y hy, ← hd, inv_mul_cancel₀ hd0]
  obtain ⟨u, hu, hub⟩ := ofReal_mem_numericalRange_of_zero_one hx hy hSx hSy ⟨hb, by linarith⟩
  refine ⟨u, hu, ?_⟩
  rw [hSu u hu] at hub
  have hua : ⟪u, T u⟫_ℂ = ⟪x, T x⟫_ℂ + (b : ℂ) * d := by
    rw [← hub]; field_simp; ring
  have ha' : (a : ℂ) = 1 - b := by
    rw [eq_sub_iff_add_eq, ← Complex.ofReal_add, hab, Complex.ofReal_one]
  rw [hua, hd, Complex.real_smul, Complex.real_smul, ha']
  ring

end Convex

section Radius

theorem bddAbove_norm_numericalRange (T : E →L[ℂ] E) :
    BddAbove ((fun z => ‖z‖) '' numericalRange T) :=
  ⟨‖T‖, by rintro _ ⟨z, hz, rfl⟩; exact norm_le_of_mem_numericalRange hz⟩

theorem numericalRadius_nonneg (T : E →L[ℂ] E) : 0 ≤ numericalRadius T :=
  Real.sSup_nonneg fun _ ⟨_, _, h⟩ => h ▸ norm_nonneg _

theorem norm_le_numericalRadius {T : E →L[ℂ] E} {z : ℂ} (hz : z ∈ numericalRange T) :
    ‖z‖ ≤ numericalRadius T :=
  le_csSup (bddAbove_norm_numericalRange T) ⟨z, hz, rfl⟩

theorem numericalRadius_le_norm (T : E →L[ℂ] E) : numericalRadius T ≤ ‖T‖ :=
  Real.sSup_le (by rintro _ ⟨z, hz, rfl⟩; exact norm_le_of_mem_numericalRange hz) (norm_nonneg T)

/-- `|⟪x, T x⟫| ≤ w(T) ‖x‖²` for every vector. -/
theorem norm_inner_map_self_le (T : E →L[ℂ] E) (x : E) :
    ‖⟪x, T x⟫_ℂ‖ ≤ numericalRadius T * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  have h := norm_le_numericalRadius (div_norm_sq_mem_numericalRange T hx)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_le_iff₀ hn] at h
  exact h

/-- `|⟪T y, x⟫| ≤ w(T) (‖x‖² + ‖y‖²)`, from the polarization identity and the parallelogram law. -/
theorem norm_inner_map_le (T : E →L[ℂ] E) (x y : E) :
    ‖⟪T y, x⟫_ℂ‖ ≤ numericalRadius T * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  set w := numericalRadius T
  have key : ∀ z : E, ‖⟪T z, z⟫_ℂ‖ ≤ w * ‖z‖ ^ 2 := fun z => by
    rw [← Complex.norm_conj, inner_conj_symm]; exact norm_inner_map_self_le T z
  have hpol := inner_map_polarization (T : E →ₗ[ℂ] E) x y
  simp only [ContinuousLinearMap.coe_coe] at hpol
  rw [hpol, norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  have hI : ‖Complex.I • y‖ = ‖y‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have p1 := parallelogram_law_with_norm ℂ x y
  have p2 := parallelogram_law_with_norm ℂ x (Complex.I • y)
  rw [hI] at p2
  have e1 := key (x + y)
  have e2 := key (x - y)
  have e3 := key (x + Complex.I • y)
  have e4 := key (x - Complex.I • y)
  calc ‖⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
          Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ‖
      ≤ ‖⟪T (x + y), x + y⟫_ℂ‖ + ‖⟪T (x - y), x - y⟫_ℂ‖ +
          ‖⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ‖ +
          ‖⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul _ ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ, Complex.norm_I, one_mul]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul]
        gcongr
        exact norm_sub_le _ _
    _ ≤ w * ‖x + y‖ ^ 2 + w * ‖x - y‖ ^ 2 + w * ‖x + Complex.I • y‖ ^ 2 +
          w * ‖x - Complex.I • y‖ ^ 2 := by gcongr
    _ = (w * (‖x‖ ^ 2 + ‖y‖ ^ 2)) * 4 := by linear_combination w * p1 + w * p2

/-- `‖T‖ ≤ 2 w(T)`. -/
theorem norm_le_two_mul_numericalRadius (T : E →L[ℂ] E) : ‖T‖ ≤ 2 * numericalRadius T := by
  set w := numericalRadius T
  have hw := numericalRadius_nonneg T
  refine T.opNorm_le_bound (by positivity) fun y => ?_
  by_cases hTy : T y = 0
  · rw [hTy, norm_zero]; positivity
  have hTn : 0 < ‖T y‖ := norm_pos_iff.mpr hTy
  set x : E := ((‖y‖ / ‖T y‖ : ℝ) : ℂ) • T y with hxdef
  have hxn : ‖x‖ = ‖y‖ := by
    rw [hxdef, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_mul_cancel₀ _ hTn.ne']
  have hinner : ⟪T y, x⟫_ℂ = ((‖y‖ * ‖T y‖ : ℝ) : ℂ) := by
    have hTc : ((‖T y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hTn.ne'
    rw [hxdef, inner_smul_right, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_eq_complex_ofReal]
    push_cast
    field_simp
  have h := norm_inner_map_le T x y
  rw [hinner, hxn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
  by_cases hy : y = 0
  · simp [hy] at hTy
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have : ‖y‖ * ‖T y‖ ≤ ‖y‖ * (2 * w * ‖y‖) := by nlinarith
  exact le_of_mul_le_mul_left this hyn

theorem eq_zero_of_numericalRadius_eq_zero {T : E →L[ℂ] E} (h : numericalRadius T = 0) : T = 0 :=
  norm_le_zero_iff.mp (by simpa [h] using norm_le_two_mul_numericalRadius T)

end Radius

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvalues of a matrix lie in the numerical range of its Euclidean operator. -/
theorem mem_numericalRange_toEuclideanCLM_of_mulVec_eq {A : Matrix n n ℂ} {μ : ℂ} {v : n → ℂ}
    (hv : v ≠ 0) (hAv : A.mulVec v = μ • v) :
    μ ∈ numericalRange (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) := by
  refine mem_numericalRange_of_eigenvector (x := WithLp.toLp 2 v) (by simpa using hv) ?_
  rw [Matrix.toEuclideanCLM_toLp, hAv, WithLp.toLp_smul]

theorem numericalRange_toEuclideanCLM_conjTranspose (A : Matrix n n ℂ) :
    numericalRange (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A.conjTranspose) =
      conj '' numericalRange (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) := by
  rw [← Matrix.star_eq_conjTranspose, map_star, numericalRange_star]

/-- Unitary similarity preserves the numerical range: `W(U A Uᴴ) = W(A)`. -/
theorem numericalRange_toEuclideanCLM_unitary_conj (A : Matrix n n ℂ)
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    numericalRange (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (U * A * U.conjTranspose)) =
      numericalRange (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A) := by
  have hu := Unitary.map_mem (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) hU
  rw [← Matrix.star_eq_conjTranspose, map_mul, map_mul, map_star]
  exact numericalRange_unitary_conj _ ⟨_, hu⟩

end Matrix

end

end TheoremOS.LinearAlgebra
