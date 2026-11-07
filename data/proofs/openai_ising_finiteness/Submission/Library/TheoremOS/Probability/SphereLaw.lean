import Mathlib

/-!
# The uniform law on the unit sphere and the standard Gaussian

For a finite-dimensional real inner product space `E` with its volume, `sphereLaw E` is the cone
measure `volume.toSphere` normalised to total mass one, a measure on the subtype
`Metric.sphere (0 : E) 1`, and `ambientSphereLaw E` is its push-forward to `E`. Contents: both are
probability measures when `E` is nontrivial; the cone formula
`sphereLaw s = volume (Ioo 0 1 • s) / volume (ball 0 1)`; invariance under every linear isometry
equivalence (`sphereMap f` restricts `f` to the sphere); `‖x‖ = 1` almost surely; the moments
`∫ ⟪x, u⟫ = 0`, `∫ ⟪x, u⟫² = ‖u‖² / dim E` and `∫ ⟪x, u⟫ ⟪x, v⟫ = ⟪u, v⟫ / dim E`; the cap lower
bound `sphereLaw (ball x ε) ≥ (min ε 2 / 4) ^ dim E`; for the standard Gaussian `stdGaussian E`,
the law of `⟪x, u⟫` is `gaussianReal 0 ‖u‖²`, `∫ ⟪x, u⟫ ⟪x, v⟫ = ⟪u, v⟫` and `∫ ‖x‖² = dim E`;
the density `stdGaussian E = volume.withDensity gaussianDensity`; and polar decomposition: every
probability measure with a radial density, in particular `stdGaussian E`, is sent to
`ambientSphereLaw E` by `x ↦ ‖x‖⁻¹ • x`.

Sources: R. Vershynin, *High-Dimensional Probability*, Cambridge University Press, 2018,
Sections 3.3–3.4 (uniform and Gaussian distributions on the sphere, rotation invariance,
isotropy); G. B. Folland, *Real Analysis*, 2nd ed., Wiley, 1999, Section 2.7 (integration in
polar coordinates); R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982,
Theorem 1.5.6 (`g / ‖g‖` is uniform on the sphere). Textbook material; nothing here is specific to
a benchmark problem.

Bridges: a statement defining `let σ := (volume : Measure V).toSphere; (σ univ)⁻¹ • σ` on
`Metric.sphere (0 : V) 1` is `sphereLaw V` by `rfl`, and its `map Subtype.val` is
`ambientSphereLaw V`, also by `rfl`. For `V = EuclideanSpace ℝ (Fin d)` the instance
`Nontrivial V` needs `NeZero d` (or `have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩`), and
`finrank_euclideanSpace_fin` rewrites `Module.finrank ℝ V` to `d`; for the ball bound use
`have h := pow_le_sphereLaw_ball (E := V) hε x; rw [finrank_euclideanSpace_fin] at h`, since
`simpa` may unfold the statement's own sphere measure. Integrals over the subtype move to
`ambientSphereLaw` with `rw [← integral_ambientSphereLaw (fun y : V => g y)]`, giving the function
explicitly so that the rewrite finds the subtype integrand.
-/

namespace TheoremOS.Probability

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

noncomputable section

section SphereLaw

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The uniform probability law on the unit sphere: the cone measure `volume.toSphere`
normalised to total mass one. -/
def sphereLaw : Measure (sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ univ)⁻¹ • σ

/-- The uniform law on the unit sphere as a measure on the ambient space. -/
def ambientSphereLaw : Measure E := (sphereLaw E).map Subtype.val

variable {E}

lemma sphereLaw_apply (s : Set (sphere (0 : E) 1)) :
    sphereLaw E s = ((volume : Measure E).toSphere univ)⁻¹ * (volume : Measure E).toSphere s := by
  simp only [sphereLaw, Measure.smul_apply, smul_eq_mul]

lemma toSphere_univ_ne_top : (volume : Measure E).toSphere univ ≠ ∞ := measure_ne_top _ _

lemma toSphere_univ_ne_zero [Nontrivial E] : (volume : Measure E).toSphere univ ≠ 0 := by
  exact Measure.measure_univ_ne_zero.mpr (volume : Measure E).toSphere_ne_zero

instance isProbabilityMeasure_sphereLaw [Nontrivial E] : IsProbabilityMeasure (sphereLaw E) :=
  ⟨by rw [sphereLaw_apply, ENNReal.inv_mul_cancel toSphere_univ_ne_zero toSphere_univ_ne_top]⟩

/-- The cone formula: the mass of `s` is the volume of the open cone over `s` divided by the volume
of the unit ball. -/
theorem sphereLaw_apply' [Nontrivial E] {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    sphereLaw E s = volume (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) / volume (ball (0 : E) 1) := by
  have hd : (Module.finrank ℝ E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [sphereLaw_apply, (volume : Measure E).toSphere_apply' hs,
    (volume : Measure E).toSphere_apply_univ, ← ENNReal.div_eq_inv_mul,
    ENNReal.mul_div_mul_left _ _ hd (ENNReal.natCast_ne_top _)]

theorem sphereLaw_real_apply' [Nontrivial E] {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    (sphereLaw E).real s =
      volume.real (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) / volume.real (ball (0 : E) 1) := by
  rw [measureReal_def, sphereLaw_apply' hs, ENNReal.toReal_div, measureReal_def, measureReal_def]

/-- A linear isometry equivalence restricted to the unit sphere. -/
def sphereMap (f : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ᵐ sphere (0 : E) 1 where
  toFun x := ⟨f x, by simp⟩
  invFun x := ⟨f.symm x, by simp⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact f.continuous.measurable.comp measurable_subtype_coe
  measurable_invFun := by
    apply Measurable.subtype_mk
    exact f.symm.continuous.measurable.comp measurable_subtype_coe

omit [FiniteDimensional ℝ E] in
@[simp] lemma coe_sphereMap (f : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (sphereMap f x : E) = f x := rfl

omit [FiniteDimensional ℝ E] in
@[simp] lemma coe_sphereMap_symm (f : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    ((sphereMap f).symm x : E) = f.symm x := rfl

omit [FiniteDimensional ℝ E] in
lemma preimage_cone_sphereMap (f : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap f ⁻¹' s) : Set E) =
      f ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  ext y
  simp only [Set.mem_smul, Set.mem_image, Set.mem_preimage, exists_exists_and_eq_and]
  constructor
  · rintro ⟨r, hr, x, hx, rfl⟩
    exact ⟨r, hr, sphereMap f x, hx, by simp [map_smul]⟩
  · rintro ⟨r, hr, x, hx, hrx⟩
    refine ⟨r, hr, (sphereMap f).symm x, by simpa using hx, ?_⟩
    apply f.injective
    simpa [map_smul] using hrx

/-- Rotation invariance of the uniform law on the sphere. -/
theorem sphereLaw_map_sphereMap (f : E ≃ₗᵢ[ℝ] E) : (sphereLaw E).map (sphereMap f) = sphereLaw E := by
  ext s hs
  rw [(sphereMap f).map_apply, sphereLaw_apply, sphereLaw_apply,
    (volume : Measure E).toSphere_apply' ((sphereMap f).measurable hs),
    (volume : Measure E).toSphere_apply' hs, preimage_cone_sphereMap,
    f.measurePreserving.measure_preimage_emb f.toHomeomorph.measurableEmbedding]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma measurableEmbedding_sphere_val : MeasurableEmbedding ((↑) : sphere (0 : E) 1 → E) :=
  MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet

instance isProbabilityMeasure_ambientSphereLaw [Nontrivial E] :
    IsProbabilityMeasure (ambientSphereLaw E) := by
  unfold ambientSphereLaw; infer_instance

lemma ambientSphereLaw_apply {s : Set E} (hs : MeasurableSet s) :
    ambientSphereLaw E s = sphereLaw E ((↑) ⁻¹' s) :=
  Measure.map_apply measurable_subtype_coe hs

/-- Rotation invariance of the ambient uniform law on the sphere. -/
theorem ambientSphereLaw_map (f : E ≃ₗᵢ[ℝ] E) : (ambientSphereLaw E).map f = ambientSphereLaw E := by
  calc (ambientSphereLaw E).map f = ((sphereLaw E).map (sphereMap f)).map (↑) := by
        rw [ambientSphereLaw, Measure.map_map f.continuous.measurable measurable_subtype_coe,
          Measure.map_map measurable_subtype_coe (sphereMap f).measurable]
        rfl
    _ = ambientSphereLaw E := by rw [sphereLaw_map_sphereMap]; rfl

lemma integral_ambientSphereLaw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) : ∫ x, g x ∂ambientSphereLaw E = ∫ x : sphere (0 : E) 1, g x ∂sphereLaw E :=
  measurableEmbedding_sphere_val.integral_map g

lemma integral_ambientSphereLaw_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E ≃ₗᵢ[ℝ] E) (g : E → F) :
    ∫ x, g (f x) ∂ambientSphereLaw E = ∫ x, g x ∂ambientSphereLaw E := by
  exact (MeasurePreserving.integral_comp ⟨f.continuous.measurable, ambientSphereLaw_map f⟩
    f.toHomeomorph.measurableEmbedding g)

lemma ae_norm_ambientSphereLaw : ∀ᵐ x ∂ambientSphereLaw E, ‖x‖ = 1 := by
  rw [ambientSphereLaw, measurableEmbedding_sphere_val.ae_map_iff]
  exact Filter.Eventually.of_forall fun x => by simp

lemma integrable_ambientSphereLaw [Nontrivial E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} (hg : Continuous g) : Integrable g (ambientSphereLaw E) := by
  rw [ambientSphereLaw, measurableEmbedding_sphere_val.integrable_map_iff]
  have : CompactSpace (sphere (0 : E) 1) := isCompact_iff_compactSpace.mp (isCompact_sphere 0 1)
  exact (hg.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma integrable_inner_ambientSphereLaw [Nontrivial E] (u : E) :
    Integrable (fun x => ⟪x, u⟫) (ambientSphereLaw E) :=
  integrable_ambientSphereLaw (by fun_prop)

lemma integrable_inner_mul_inner_ambientSphereLaw [Nontrivial E] (u v : E) :
    Integrable (fun x => ⟪x, u⟫ * ⟪x, v⟫) (ambientSphereLaw E) :=
  integrable_ambientSphereLaw (by fun_prop)

lemma integrable_inner_sq_ambientSphereLaw [Nontrivial E] (u : E) :
    Integrable (fun x => ⟪x, u⟫ ^ 2) (ambientSphereLaw E) :=
  integrable_ambientSphereLaw (by fun_prop)

/-- The uniform law on the sphere is centred. -/
theorem integral_inner_ambientSphereLaw (u : E) : ∫ x, ⟪x, u⟫ ∂ambientSphereLaw E = 0 := by
  have h := integral_ambientSphereLaw_comp (LinearIsometryEquiv.neg ℝ) (fun x => ⟪x, u⟫)
  simp only [LinearIsometryEquiv.coe_neg, inner_neg_left, integral_neg] at h
  linarith

lemma integral_inner_sq_ambientSphereLaw_eq {u v : E} (h : ‖u‖ = ‖v‖) :
    ∫ x, ⟪x, u⟫ ^ 2 ∂ambientSphereLaw E = ∫ x, ⟪x, v⟫ ^ 2 ∂ambientSphereLaw E := by
  set ρ := Submodule.reflection (ℝ ∙ (u - v))ᗮ
  have hρ : ρ u = v := Submodule.reflection_sub h
  have key := integral_ambientSphereLaw_comp ρ (fun x => ⟪x, v⟫ ^ 2)
  have hpt : ∀ x, ⟪ρ x, v⟫ = ⟪x, u⟫ := fun x => by
    rw [← hρ, LinearIsometryEquiv.inner_map_map]
  simp_rw [hpt] at key
  exact key

lemma sum_integral_inner_sq_ambientSphereLaw [Nontrivial E] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : ∑ i, ∫ x, ⟪x, b i⟫ ^ 2 ∂ambientSphereLaw E = 1 := by
  rw [← integral_finsetSum _ fun i _ => integrable_inner_sq_ambientSphereLaw (b i)]
  have hsum : ∀ x : E, ∑ i, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := b.sum_sq_inner_left
  simp_rw [hsum]
  rw [integral_congr_ae (ae_norm_ambientSphereLaw.mono fun x hx => by simp [hx] :
    (fun x : E => ‖x‖ ^ 2) =ᵐ[ambientSphereLaw E] fun _ => (1 : ℝ))]
  simp

/-- Isotropy: `∫ ⟪x, u⟫² = ‖u‖² / dim E` under the uniform law on the sphere. -/
theorem integral_inner_sq_ambientSphereLaw [Nontrivial E] (u : E) :
    ∫ x, ⟪x, u⟫ ^ 2 ∂ambientSphereLaw E = ‖u‖ ^ 2 / Module.finrank ℝ E := by
  set d := Module.finrank ℝ E
  have hd : 0 < d := Module.finrank_pos
  let b := stdOrthonormalBasis ℝ E
  let i₀ : Fin d := ⟨0, hd⟩
  have hall : ∀ i, ∫ x, ⟪x, b i⟫ ^ 2 ∂ambientSphereLaw E = ∫ x, ⟪x, b i₀⟫ ^ 2 ∂ambientSphereLaw E :=
    fun i => integral_inner_sq_ambientSphereLaw_eq (by rw [b.orthonormal.1 i, b.orthonormal.1 i₀])
  have hone := sum_integral_inner_sq_ambientSphereLaw b
  simp_rw [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hone
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hJ : ∫ x, ⟪x, b i₀⟫ ^ 2 ∂ambientSphereLaw E = 1 / d := by
    rw [eq_div_iff hdR.ne']; linarith
  by_cases hu : u = 0
  · simp [hu]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set w : E := ‖u‖⁻¹ • u
  have hw : ‖w‖ = ‖b i₀‖ := by
    rw [b.orthonormal.1 i₀, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hpt : ∀ x, ⟪x, u⟫ ^ 2 = ‖u‖ ^ 2 * ⟪x, w⟫ ^ 2 := fun x => by
    have : u = ‖u‖ • w := by simp [w, smul_smul, mul_inv_cancel₀ hn.ne']
    conv_lhs => rw [this]
    rw [real_inner_smul_right, mul_pow]
  simp_rw [hpt]
  rw [integral_const_mul, integral_inner_sq_ambientSphereLaw_eq hw, hJ]
  ring

/-- `∫ ⟪x, u⟫ ⟪x, v⟫ = ⟪u, v⟫ / dim E` under the uniform law on the sphere. -/
theorem integral_inner_mul_inner_ambientSphereLaw [Nontrivial E] (u v : E) :
    ∫ x, ⟪x, u⟫ * ⟪x, v⟫ ∂ambientSphereLaw E = ⟪u, v⟫ / Module.finrank ℝ E := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  have h := integral_inner_sq_ambientSphereLaw (E := E) (u + v)
  have hpt : ∀ x, ⟪x, u + v⟫ ^ 2 = ⟪x, u⟫ ^ 2 + ⟪x, v⟫ ^ 2 + 2 * (⟪x, u⟫ * ⟪x, v⟫) :=
    fun x => by rw [inner_add_right]; ring
  simp_rw [hpt] at h
  have i1 := integrable_inner_sq_ambientSphereLaw (E := E) u
  have i2 := integrable_inner_sq_ambientSphereLaw (E := E) v
  have i3 := (integrable_inner_mul_inner_ambientSphereLaw (E := E) u v).const_mul 2
  have i12 : Integrable (fun x => ⟪x, u⟫ ^ 2 + ⟪x, v⟫ ^ 2) (ambientSphereLaw E) := i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_inner_sq_ambientSphereLaw, integral_inner_sq_ambientSphereLaw, norm_add_sq_real] at h
  field_simp at h ⊢
  linarith

/-- Cap lower bound: a ball of radius `ε` around a point of the sphere has mass at least
`(min ε 2 / 4) ^ dim E`. -/
theorem pow_le_sphereLaw_ball {ε : ℝ} (hε : 0 < ε) (x : sphere (0 : E) 1) :
    (min ε 2 / 4) ^ Module.finrank ℝ E ≤ (sphereLaw E).real (ball x ε) := by
  have : Nontrivial E := ⟨⟨x, 0, ne_of_apply_ne norm (by simp)⟩⟩
  set d := Module.finrank ℝ E
  have hd : (0 : ℝ) < d := by exact_mod_cast Module.finrank_pos
  have hB : 0 < (volume : Measure E).real (ball 0 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  have h := (volume : Measure E).toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball hε x
  have hbound : (Measure.toSphereBallBound d ε : ℝ) = d * (min ε 2 / 4) ^ d := by
    rw [Measure.toSphereBallBound, ite_eq_left ⟨Module.finrank_pos.ne', hε⟩]
    push_cast
    rw [Real.coe_toNNReal _ hε.le]
  rw [hbound] at h
  have hsl : (sphereLaw E).real (ball x ε) =
      (volume : Measure E).toSphere.real (ball x ε) / (d * (volume : Measure E).real (ball 0 1)) := by
    rw [measureReal_def, sphereLaw_apply, ← ENNReal.div_eq_inv_mul, ENNReal.toReal_div,
      ← measureReal_def, ← measureReal_def, Measure.toSphere_real_apply_univ]
  rw [hsl, le_div_iff₀ (mul_pos hd hB)]
  nlinarith

end SphereLaw

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma memLp_inner_stdGaussian (u : E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x => ⟪x, u⟫) p (stdGaussian E) := by
  have h := IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ u) p hp
  refine h.congr_norm (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_comm]

lemma integrable_inner_mul_inner_stdGaussian (u v : E) :
    Integrable (fun x => ⟪x, u⟫ * ⟪x, v⟫) (stdGaussian E) :=
  (memLp_inner_stdGaussian u 2 (by simp)).integrable_mul (memLp_inner_stdGaussian v 2 (by simp))

lemma integrable_inner_sq_stdGaussian (u : E) :
    Integrable (fun x => ⟪x, u⟫ ^ 2) (stdGaussian E) := by
  simpa [sq] using integrable_inner_mul_inner_stdGaussian u u

/-- Under the standard Gaussian, `⟪x, u⟫` has law `N(0, ‖u‖²)`. -/
theorem stdGaussian_map_inner (u : E) :
    (stdGaussian E).map (fun x => ⟪x, u⟫) = gaussianReal 0 (‖u‖₊ ^ 2) := by
  have hf : (fun x : E => ⟪x, u⟫) = innerSL ℝ u := by
    funext x; simp [real_inner_comm]
  rw [hf, IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, innerSL_apply_norm]
  congr 1
  ext
  simp

theorem stdGaussian_map_inner_of_norm_eq_one {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun x => ⟪x, u⟫) = gaussianReal 0 1 := by
  rw [stdGaussian_map_inner]
  congr 1
  ext
  simp [hu]

/-- The standard Gaussian is isotropic: `∫ ⟪x, u⟫ ⟪x, v⟫ = ⟪u, v⟫`. -/
theorem integral_inner_mul_inner_stdGaussian (u v : E) :
    ∫ x, ⟪x, u⟫ * ⟪x, v⟫ ∂stdGaussian E = ⟪u, v⟫ := by
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id u v
  rw [covarianceBilin_stdGaussian] at h
  simp only [id_eq, integral_id_stdGaussian, sub_zero] at h
  rw [innerSL_apply_apply] at h
  rw [h]
  congr 1
  funext x
  rw [real_inner_comm x u, real_inner_comm x v]

theorem integral_inner_sq_stdGaussian (u : E) : ∫ x, ⟪x, u⟫ ^ 2 ∂stdGaussian E = ‖u‖ ^ 2 := by
  simpa [sq, real_inner_self_eq_norm_sq] using integral_inner_mul_inner_stdGaussian u u

theorem integral_norm_sq_stdGaussian : ∫ x, ‖x‖ ^ 2 ∂stdGaussian E = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hsum : ∀ x : E, ‖x‖ ^ 2 = ∑ i, ⟪x, b i⟫ ^ 2 := fun x => (b.sum_sq_inner_left x).symm
  simp_rw [hsum]
  rw [integral_finsetSum _ fun i _ => integrable_inner_sq_stdGaussian (b i)]
  simp [integral_inner_sq_stdGaussian, b.orthonormal.1]

variable (E) in
/-- The standard Gaussian density `(2π)^{-d/2} exp(-‖x‖²/2)` on `E`, `d = dim E`. -/
def gaussianDensity (x : E) : ℝ :=
  ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ * Real.exp (-‖x‖ ^ 2 / 2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gaussianDensity_nonneg (x : E) : 0 ≤ gaussianDensity E x := by
  unfold gaussianDensity; positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_gaussianDensity : Continuous (gaussianDensity E) := by
  unfold gaussianDensity; fun_prop

end Gaussian

section Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma integrable_exp_neg_sq_norm_div_two : Integrable (fun x : E => Real.exp (-‖x‖ ^ 2 / 2)) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1 / 2) (by norm_num)
  have hne : ∫ x : E, Real.exp (-(1 / 2) * ‖x‖ ^ 2) ≠ 0 := by rw [h]; positivity
  have hf : (fun x : E => Real.exp (-‖x‖ ^ 2 / 2)) = fun x => Real.exp (-(1 / 2) * ‖x‖ ^ 2) := by
    funext x; congr 1; ring
  rw [hf]
  exact Integrable.of_integral_ne_zero hne

lemma integrable_gaussianDensity : Integrable (gaussianDensity E) :=
  integrable_exp_neg_sq_norm_div_two.const_mul _

lemma charFun_withDensity_gaussianDensity (t : E) :
    charFun ((volume : Measure E).withDensity fun x => ENNReal.ofReal (gaussianDensity E x)) t =
      Complex.exp (-(‖t‖ : ℂ) ^ 2 / 2) := by
  set c : ℝ := ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul
    (continuous_gaussianDensity.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hpt : ∀ x : E, (ENNReal.ofReal (gaussianDensity E x)).toReal •
      Complex.exp (⟪x, t⟫ * Complex.I) =
      (c : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (‖x‖ : ℂ) ^ 2 + Complex.I * (⟪t, x⟫ : ℂ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (gaussianDensity_nonneg x), Complex.real_smul, gaussianDensity,
      Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp, ← Complex.exp_add, real_inner_comm t x]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := E)
    (b := 1 / 2) (by norm_num) Complex.I t, ← mul_assoc]
  have hpos : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hcpow : ((Real.pi : ℂ) / (1 / 2)) ^ ((Module.finrank ℝ E : ℂ) / 2) =
      (((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hpos]
    push_cast
    congr 1
    ring
  have hne : (((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by positivity) _).ne'
  rw [hcpow, Complex.ofReal_inv, inv_mul_cancel₀ hne, one_mul, Complex.I_sq]
  congr 1
  ring

/-- The standard Gaussian has density `gaussianDensity E` with respect to volume. -/
theorem stdGaussian_eq_withDensity :
    stdGaussian E = (volume : Measure E).withDensity fun x => ENNReal.ofReal (gaussianDensity E x) := by
  have : IsFiniteMeasure ((volume : Measure E).withDensity
      fun x => ENNReal.ofReal (gaussianDensity E x)) :=
    isFiniteMeasure_withDensity_ofReal integrable_gaussianDensity.hasFiniteIntegral
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_stdGaussian, charFun_withDensity_gaussianDensity]

lemma measurable_normalize : Measurable fun x : E => ‖x‖⁻¹ • x :=
  (measurable_norm.inv).smul measurable_id

/-- Polar decomposition of a radial law: if `ν` is a probability measure with density `g ‖x‖`
with respect to volume, then the direction `x ↦ ‖x‖⁻¹ • x` has the uniform law on the sphere. -/
theorem map_normalize_of_radial [Nontrivial E] (ν : Measure E) [IsProbabilityMeasure ν]
    {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    (hν : ν = (volume : Measure E).withDensity fun x => g ‖x‖) :
    ν.map (fun x => ‖x‖⁻¹ • x) = ambientSphereLaw E := by
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  have hmp := (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  set R := ∫⁻ r, g r ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
  have key : ∀ B : Set E, MeasurableSet B →
      ν ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B) =
        (volume : Measure E).toSphere ((↑) ⁻¹' B) * R := by
    intro B hB
    have hS : MeasurableSet ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B) := measurable_normalize hB
    have hB' : MeasurableSet (((↑) : sphere (0 : E) 1 → E) ⁻¹' B) :=
      measurable_subtype_coe hB
    have hpt : ∀ z : ({0}ᶜ : Set E),
        ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B).indicator (fun x => g ‖x‖) (z : E) =
          (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            (((↑) : sphere (0 : E) 1 → E) ⁻¹' B).indicator 1 p.1 * g p.2)
            (homeomorphUnitSphereProd E z) := by
      intro z
      classical
      simp only [Set.indicator_apply, Set.mem_preimage, homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_apply_snd_coe, Pi.one_apply]
      split_ifs <;> simp
    rw [hν, withDensity_apply _ hS, ← lintegral_indicator hS]
    calc ∫⁻ x, ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B).indicator (fun x => g ‖x‖) x
          = ∫⁻ x in ({0}ᶜ : Set E),
              ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B).indicator (fun x => g ‖x‖) x := by
            rw [restrict_compl_singleton]
      _ = ∫⁻ z : ({0}ᶜ : Set E),
              ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' B).indicator (fun x => g ‖x‖) (z : E)
              ∂(volume : Measure E).comap (↑) :=
            (lintegral_subtype_comap (measurableSet_singleton _).compl _).symm
      _ = ∫⁻ p, (((↑) : sphere (0 : E) 1 → E) ⁻¹' B).indicator 1 p.1 * g p.2
              ∂((volume : Measure E).toSphere.prod
                (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
            simp_rw [hpt]
            exact hmp.lintegral_comp_emb hemb
              (fun p => (((↑) : sphere (0 : E) 1 → E) ⁻¹' B).indicator 1 p.1 * g p.2)
      _ = (∫⁻ s, (((↑) : sphere (0 : E) 1 → E) ⁻¹' B).indicator 1 s
              ∂(volume : Measure E).toSphere) * R :=
            lintegral_prod_mul ((measurable_one.indicator hB').aemeasurable)
              ((hg.comp measurable_subtype_coe).aemeasurable)
      _ = (volume : Measure E).toSphere ((↑) ⁻¹' B) * R := by
            rw [lintegral_indicator_one hB']
  have hR : R = ((volume : Measure E).toSphere univ)⁻¹ := by
    have h1 := key univ MeasurableSet.univ
    simp only [Set.preimage_univ, measure_univ] at h1
    rw [mul_comm] at h1
    exact ENNReal.eq_inv_of_mul_eq_one_left h1.symm
  ext B hB
  rw [Measure.map_apply measurable_normalize hB, key B hB, hR, ambientSphereLaw_apply hB,
    sphereLaw_apply, mul_comm]

/-- If `g` is a standard Gaussian vector then `g / ‖g‖` is uniform on the sphere. -/
theorem stdGaussian_map_normalize [Nontrivial E] :
    (stdGaussian E).map (fun x => ‖x‖⁻¹ • x) = ambientSphereLaw E :=
  map_normalize_of_radial (stdGaussian E)
    (g := fun r => ENNReal.ofReal
      (((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ * Real.exp (-r ^ 2 / 2)))
    (by fun_prop) stdGaussian_eq_withDensity

/-- Integrals against the uniform law on the sphere as Gaussian integrals of the direction. -/
theorem integral_ambientSphereLaw_eq_stdGaussian [Nontrivial E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : AEStronglyMeasurable f
      (ambientSphereLaw E)) :
    ∫ x, f x ∂ambientSphereLaw E = ∫ x, f (‖x‖⁻¹ • x) ∂stdGaussian E := by
  rw [← stdGaussian_map_normalize] at hf ⊢
  exact integral_map measurable_normalize.aemeasurable hf

end Polar


end

end TheoremOS.Probability
