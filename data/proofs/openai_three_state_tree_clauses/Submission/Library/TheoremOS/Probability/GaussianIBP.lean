import Submission.Library.TheoremOS.Probability.SphereLaw

/-!
# Gaussian integration by parts

Stein's identity and its multivariate forms. Contents: for `X ~ gaussianReal μ v`,
`E[(X - μ) • f X] = v • E[f' X]` when `f` has derivative `f'` everywhere and the three integrals
exist (`integral_sub_smul_gaussianReal`, real form `integral_sub_mul_gaussianReal`), the case
`v = 0` included; the same with the integrability conditions replaced by polynomial growth bounds
`‖f x‖, ‖f' x‖ ≤ C (1 + ‖x‖)^k` (`_of_growth`, centred form
`integral_mul_gaussianReal_zero_of_growth`), using that polynomially bounded measurable functions
are integrable for every `IsGaussian` measure (`integrable_of_norm_le_poly`); the central moments
`E[(X - μ)^(n+2)] = (n+1) v E[(X - μ)^n]`, odd central moments `0` and
`E[(X - μ)^(2n)] = v^n ∏_{i<n} (2i+1)`; the derivative of `gaussianPDFReal`; for the standard
Gaussian `stdGaussian E` on a finite-dimensional inner product space,
`E[⟪x, u⟫ • f x] = E[f' x u]` for Fréchet-differentiable `f` (`integral_inner_smul_stdGaussian`,
with a polynomial-growth form); for independent coordinates
`Measure.pi fun j => gaussianReal 0 (v j)` on `ι → ℝ`,
`E[x i • f x] = v i • E[f' x (Pi.single i 1)]` (`integral_coord_smul_pi_gaussianReal`, zero
variances allowed, with a polynomial-growth form in the sup norm), via `pi_gaussianReal_eq_map`,
the product as the image of `stdGaussian` under the coordinatewise scaling `gaussianScale v`; for
an affine image `y = m + A x` of `stdGaussian`,
`E[⟪y - m, w⟫ • f y] = E[f' y (A (A† w))]`; and for `multivariateGaussian μ S` with `S`
positive semidefinite, `E[⟪y - μ, w⟫ • f y] = E[f' y (S w)]`.

Sources: C. M. Stein, "Estimation of the mean of a multivariate normal distribution", Ann.
Statist. 9 (1981), 1135–1151, Lemmas 1–2 (one-dimensional and multivariate identities);
I. Nourdin and G. Peccati, *Normal Approximations with Malliavin Calculus*, Cambridge University
Press, 2012, Chapters 3–4 (Stein's lemma, multivariate Gaussian integration by parts);
M. Talagrand, *Mean Field Models for Spin Glasses*, Vol. I, Springer, 2011, and D. Panchenko,
*The Sherrington–Kirkpatrick Model*, Springer, 2013, Chapter 1 (Gaussian integration by parts for
independent coordinates); P. Billingsley, *Probability and Measure*, 3rd ed., Wiley, 1995,
Section 21 (moments of the normal distribution). Textbook material; nothing here is specific to a
benchmark problem.

Bridges: a disorder law `Measure.pi fun _ : I => gaussianReal 0 σ` is the coordinate form with
`v := fun _ => σ`, so `simpa [disorderLaw] using integral_coord_mul_pi_gaussianReal_of_growth
(fun _ => σ) e hf hfb hf'b` gives `∫ W, W e * f W = σ * ∫ W, f' W (Pi.single e 1)`; definitions
such as `standardGaussian := gaussianReal 0 1` and `gaussianProduct ι := Measure.pi fun _ =>
standardGaussian` unfold the same way with `v := fun _ => 1`. A coordinate function `W ↦ W e` has
derivative `hasFDerivAt_apply e W` with `‖ContinuousLinearMap.proj e‖ ≤ 1` from
`ContinuousLinearMap.opNorm_le_bound` and `norm_le_pi_norm`; for a differentiable `f` take
`f' := fderiv ℝ f` with `(hdiff x).hasFDerivAt`. For a shifted argument,
`∫ z, z * U (x + √s * z) ∂gaussianReal 0 1 = √s * ∫ z, U' (x + √s * z) ∂gaussianReal 0 1` follows
from `integral_mul_gaussianReal_zero_of_growth` after first proving
`HasDerivAt (fun z => x + √s * z) √s z` with
`simpa using ((hasDerivAt_id' z).const_mul _).const_add x`
(composing directly leaves `√s * 1`). The growth forms do not cover exponentially growing
integrands such as partition functions, which need the integrable forms, and nested products
`Measure.pi fun _ => Measure.pi fun _ => …` must first be identified with a single product.
-/

namespace TheoremOS.Probability

open MeasureTheory ProbabilityTheory Set Real Matrix
open scoped ENNReal NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

noncomputable section

section Growth

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

/-- Under a Gaussian law every function of polynomial growth is integrable. -/
lemma integrable_of_norm_le_poly (ν : Measure E) [IsGaussian ν] {g : E → F}
    (hg : AEStronglyMeasurable g ν) {C : ℝ} {k : ℕ} (hb : ∀ x, ‖g x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Integrable g ν := by
  have h1 : MemLp (fun x : E => ‖x‖) k ν :=
    (IsGaussian.memLp_id ν k (ENNReal.natCast_ne_top k)).norm
  have hm := (memLp_const (μ := ν) (p := (k : ℝ≥0∞)) (1 : ℝ)).add h1
  have hi : Integrable (fun x : E => (1 + ‖x‖) ^ k) ν := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero]; exact integrable_const 1
    · refine (hm.integrable_norm_pow hk.ne').congr (ae_of_all _ fun x => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖)]
  exact (hi.const_mul C).mono' hg (ae_of_all _ hb)

end Growth

section Real

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {μ : ℝ} {v : ℝ≥0}

/-- The Gaussian density solves `p' = -((x - μ) / v) p`. -/
lemma hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-((x - μ) / v) * gaussianPDFReal μ v x) x := by
  have h : HasDerivAt (fun y => -(y - μ) ^ 2 / (2 * (v : ℝ))) (-(2 * (x - μ)) / (2 * v)) x := by
    have := ((hasDerivAt_id x).sub_const μ).pow 2
    simpa using (this.neg).div_const (2 * (v : ℝ))
  have h2 := (h.exp).const_mul (√(2 * π * v))⁻¹
  rw [gaussianPDFReal_def]
  convert h2 using 1
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  · field_simp

omit [CompleteSpace F] in
lemma integrable_gaussianReal_iff (hv : v ≠ 0) {f : ℝ → F} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x • f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp [gaussianPDF, gaussianPDFReal_nonneg]

/-- **Stein's identity** for `N(μ, v)`: `E[(X - μ) f(X)] = v E[f'(X)]`, for `f` with derivative
`f'` such that `f`, `(x - μ) • f x` and `f'` are integrable. The case `v = 0` is the Dirac mass. -/
theorem integral_sub_smul_gaussianReal {f f' : ℝ → F} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal μ v))
    (hxf : Integrable (fun x => (x - μ) • f x) (gaussianReal μ v))
    (hf' : Integrable f' (gaussianReal μ v)) :
    ∫ x, (x - μ) • f x ∂gaussianReal μ v = (v : ℝ) • ∫ x, f' x ∂gaussianReal μ v := by
  by_cases hv : v = 0
  · rw [hv, gaussianReal_zero_var, integral_dirac]
    simp
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [integrable_gaussianReal_iff hv] at hfi hxf hf'
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  have hp' : Integrable fun x =>
      ContinuousLinearMap.lsmul ℝ ℝ (-((x - μ) / v) * gaussianPDFReal μ v x) (f x) := by
    refine (hxf.smul (-(v : ℝ)⁻¹)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.smul_apply, ContinuousLinearMap.lsmul_apply, smul_smul]
    congr 1
    ring
  have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (u := gaussianPDFReal μ v) (v := f)
    (u' := fun x => -((x - μ) / v) * gaussianPDFReal μ v x) (v' := f')
    (fun x _ => hasDerivAt_gaussianPDFReal μ v x) (fun x _ => hf x)
    (by simpa using hf') hp' (by simpa using hfi)
  simp only [ContinuousLinearMap.lsmul_apply] at h
  have h3 : ∫ x, gaussianPDFReal μ v x • (x - μ) • f x =
      -(v : ℝ) • ∫ x, (-((x - μ) / v) * gaussianPDFReal μ v x) • f x := by
    rw [← integral_smul]
    congr 1
    funext x
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  rw [h3, h, smul_neg, neg_smul]

/-- Real-valued Stein identity: `∫ (x - μ) f(x) = v ∫ f'(x)` under `N(μ, v)`. -/
theorem integral_sub_mul_gaussianReal {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfi : Integrable f (gaussianReal μ v))
    (hxf : Integrable (fun x => (x - μ) * f x) (gaussianReal μ v))
    (hf' : Integrable f' (gaussianReal μ v)) :
    ∫ x, (x - μ) * f x ∂gaussianReal μ v = v * ∫ x, f' x ∂gaussianReal μ v :=
  integral_sub_smul_gaussianReal hf hfi hxf hf'

omit [CompleteSpace F] in
lemma norm_sub_smul_le {f : ℝ → F} {C : ℝ} {k : ℕ} (hb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (x : ℝ) : ‖(x - μ) • f x‖ ≤ (1 + ‖μ‖) * C * (1 + ‖x‖) ^ (k + 1) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have h1 : ‖x - μ‖ ≤ (1 + ‖μ‖) * (1 + ‖x‖) := by
    nlinarith [norm_sub_le x μ, norm_nonneg x, norm_nonneg μ,
      mul_nonneg (norm_nonneg x) (norm_nonneg μ)]
  rw [norm_smul]
  calc ‖x - μ‖ * ‖f x‖ ≤ ((1 + ‖μ‖) * (1 + ‖x‖)) * (C * (1 + ‖x‖) ^ k) :=
        mul_le_mul h1 (hb x) (norm_nonneg _) (by positivity)
    _ = (1 + ‖μ‖) * C * (1 + ‖x‖) ^ (k + 1) := by ring

/-- Stein's identity for `N(μ, v)` when `f` and `f'` grow at most polynomially; the integrability
side conditions are discharged automatically. -/
theorem integral_sub_smul_gaussianReal_of_growth {f f' : ℝ → F} (hf : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {k : ℕ} (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf'b : ∀ x, ‖f' x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, (x - μ) • f x ∂gaussianReal μ v = (v : ℝ) • ∫ x, f' x ∂gaussianReal μ v := by
  have hc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hd : f' = deriv f := funext fun x => (hf x).deriv.symm
  have hm' : AEStronglyMeasurable f' (gaussianReal μ v) := by
    rw [hd]; exact aestronglyMeasurable_deriv f _
  refine integral_sub_smul_gaussianReal hf
    (integrable_of_norm_le_poly _ hc.aestronglyMeasurable hfb) ?_
    (integrable_of_norm_le_poly _ hm' hf'b)
  exact integrable_of_norm_le_poly _ (by fun_prop) (norm_sub_smul_le hfb)

/-- Centred Stein identity `E[X f(X)] = v E[f'(X)]` for `X ~ N(0, v)` and real `f`, `f'` of
polynomial growth. -/
theorem integral_mul_gaussianReal_zero_of_growth {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {k : ℕ} (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf'b : ∀ x, ‖f' x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, x * f x ∂gaussianReal 0 v = v * ∫ x, f' x ∂gaussianReal 0 v := by
  simpa using integral_sub_smul_gaussianReal_of_growth (μ := 0) (v := v) hf hfb hf'b

lemma integrable_sub_pow_gaussianReal (n : ℕ) :
    Integrable (fun x => (x - μ) ^ n) (gaussianReal μ v) := by
  have h : MemLp (fun x : ℝ => x - μ) n (gaussianReal μ v) :=
    (memLp_id_gaussianReal n).sub (memLp_const μ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (h.integrable_norm_pow hn.ne').mono'
      (by fun_prop : Continuous fun x : ℝ => (x - μ) ^ n).aestronglyMeasurable
      (ae_of_all _ fun x => (norm_pow _ _).le)

/-- Central moment recursion: `E[(X - μ)^(n+2)] = (n+1) v E[(X - μ)^n]` under `N(μ, v)`. -/
theorem integral_sub_pow_add_two_gaussianReal (n : ℕ) :
    ∫ x, (x - μ) ^ (n + 2) ∂gaussianReal μ v =
      (n + 1) * v * ∫ x, (x - μ) ^ n ∂gaussianReal μ v := by
  have hd : ∀ x, HasDerivAt (fun y => (y - μ) ^ (n + 1)) ((n + 1 : ℝ) * (x - μ) ^ n) x := by
    intro x
    simpa using ((hasDerivAt_id' x).sub_const μ).fun_pow (n + 1)
  have h := integral_sub_mul_gaussianReal (μ := μ) (v := v) hd
    (integrable_sub_pow_gaussianReal (n + 1))
    ((integrable_sub_pow_gaussianReal (n + 2)).congr (ae_of_all _ fun x => by
      show (x - μ) ^ (n + 2) = (x - μ) * (x - μ) ^ (n + 1); ring))
    ((integrable_sub_pow_gaussianReal n).const_mul _)
  have hl : ∫ x, (x - μ) ^ (n + 2) ∂gaussianReal μ v =
      ∫ x, (x - μ) * (x - μ) ^ (n + 1) ∂gaussianReal μ v := by
    congr 1; funext x; ring
  rw [hl, h, integral_const_mul]
  ring

theorem integral_sub_pow_odd_gaussianReal (n : ℕ) :
    ∫ x, (x - μ) ^ (2 * n + 1) ∂gaussianReal μ v = 0 := by
  induction n with
  | zero =>
    simp only [mul_zero, zero_add, pow_one]
    have hi : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
      (memLp_id_gaussianReal 1).integrable le_rfl
    rw [integral_sub hi (integrable_const μ)]
    simp [integral_id_gaussianReal]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 2 by ring, integral_sub_pow_add_two_gaussianReal, ih,
      mul_zero]

/-- Even central moments: `E[(X - μ)^(2n)] = v^n ∏_{i<n} (2i+1) = v^n (2n-1)!!`. -/
theorem integral_sub_pow_even_gaussianReal (n : ℕ) :
    ∫ x, (x - μ) ^ (2 * n) ∂gaussianReal μ v =
      (v : ℝ) ^ n * ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, integral_sub_pow_add_two_gaussianReal, ih,
      Finset.prod_range_succ]
    push_cast
    ring

end Real

section Std

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The standard Gaussian density `φ` satisfies `∇φ(x) = -φ(x) x`. -/
lemma hasFDerivAt_gaussianDensity (x : E) :
    HasFDerivAt (gaussianDensity E) (-gaussianDensity E x • innerSL ℝ x) x := by
  have h1 := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (-(1 / 2 : ℝ))).exp).const_mul
    ((2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹
  have he : gaussianDensity E =
      fun y => ((2 * π) ^ ((Module.finrank ℝ E : ℝ) / 2))⁻¹ *
        Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2) := by
    funext y; rw [gaussianDensity]; congr 2; ring
  rw [he]
  convert h1 using 1
  ext u
  simp
  ring

lemma integral_stdGaussian_eq_integral_smul (g : E → F) :
    ∫ x, g x ∂stdGaussian E = ∫ x, gaussianDensity E x • g x := by
  rw [stdGaussian_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    continuous_gaussianDensity.measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp [gaussianDensity_nonneg]

lemma integrable_stdGaussian_iff {g : E → F} :
    Integrable g (stdGaussian E) ↔ Integrable (fun x => gaussianDensity E x • g x) := by
  rw [stdGaussian_eq_withDensity, integrable_withDensity_iff_integrable_smul'
    continuous_gaussianDensity.measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp [gaussianDensity_nonneg]

/-- **Gaussian integration by parts** on a finite-dimensional inner product space:
`E[⟪X, u⟫ f(X)] = E[f'(X) u]` for `X` standard Gaussian, when `f`, `⟪x, u⟫ • f x` and `f' x u`
are integrable. -/
theorem integral_inner_smul_stdGaussian {f : E → F} {f' : E → E →L[ℝ] F} (u : E)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hfi : Integrable f (stdGaussian E))
    (hxf : Integrable (fun x => ⟪x, u⟫ • f x) (stdGaussian E))
    (hf' : Integrable (fun x => f' x u) (stdGaussian E)) :
    ∫ x, ⟪x, u⟫ • f x ∂stdGaussian E = ∫ x, f' x u ∂stdGaussian E := by
  rw [integrable_stdGaussian_iff] at hfi hxf hf'
  rw [integral_stdGaussian_eq_integral_smul, integral_stdGaussian_eq_integral_smul]
  have hp' : Integrable fun x => ContinuousLinearMap.lsmul ℝ ℝ
      ((-gaussianDensity E x • innerSL ℝ x) u) (f x) := by
    refine hxf.neg.congr (ae_of_all _ fun x => ?_)
    simp [smul_smul]
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := gaussianDensity E) (g := f) (v := u)
    (f' := fun x => -gaussianDensity E x • innerSL ℝ x) (g' := f')
    hp' (by simpa using hf') (by simpa using hfi)
    (fun x _ => hasFDerivAt_gaussianDensity x) (fun x _ => hf x)
  simp only [ContinuousLinearMap.lsmul_apply] at h
  rw [h, ← integral_neg]
  congr 1
  funext x
  simp [smul_smul]

/-- Real-valued Gaussian integration by parts: `∫ ⟪x, u⟫ f(x) = ∫ f'(x) u`. -/
theorem integral_inner_mul_stdGaussian {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} (u : E)
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hfi : Integrable f (stdGaussian E))
    (hxf : Integrable (fun x => ⟪x, u⟫ * f x) (stdGaussian E))
    (hf' : Integrable (fun x => f' x u) (stdGaussian E)) :
    ∫ x, ⟪x, u⟫ * f x ∂stdGaussian E = ∫ x, f' x u ∂stdGaussian E :=
  integral_inner_smul_stdGaussian u hf hfi hxf hf'

/-- Gaussian integration by parts for real `f` whose value and derivative grow at most
polynomially, `|f x| ≤ C (1 + ‖x‖)^k` and `‖f' x‖ ≤ C (1 + ‖x‖)^k`. -/
theorem integral_inner_mul_stdGaussian_of_growth {f : E → ℝ} {f' : E → E →L[ℝ] ℝ} (u : E)
    (hf : ∀ x, HasFDerivAt f (f' x) x) {C : ℝ} {k : ℕ} (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf'b : ∀ x, ‖f' x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, ⟪x, u⟫ * f x ∂stdGaussian E = ∫ x, f' x u ∂stdGaussian E := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hfb 0)
  have hc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hd : (fun x => f' x u) = fun x => fderiv ℝ f x u := funext fun x => by rw [(hf x).fderiv]
  have hm : AEStronglyMeasurable (fun x => f' x u) (stdGaussian E) := by
    rw [hd]; exact (measurable_fderiv_apply_const ℝ f u).aestronglyMeasurable
  refine integral_inner_mul_stdGaussian u hf
    (integrable_of_norm_le_poly _ hc.aestronglyMeasurable hfb) ?_
    (integrable_of_norm_le_poly _ hm (C := ‖u‖ * C) (k := k) fun x => ?_)
  · refine integrable_of_norm_le_poly _ (by fun_prop) (C := ‖u‖ * C) (k := k + 1) fun x => ?_
    rw [norm_mul]
    calc ‖⟪x, u⟫‖ * ‖f x‖ ≤ (‖u‖ * (1 + ‖x‖)) * (C * (1 + ‖x‖) ^ k) := by
          refine mul_le_mul ?_ (hfb x) (norm_nonneg _) (by positivity)
          rw [real_inner_comm]
          refine (norm_inner_le_norm u x).trans ?_
          exact mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) (norm_nonneg u)
      _ = ‖u‖ * C * (1 + ‖x‖) ^ (k + 1) := by ring
  · calc ‖f' x u‖ ≤ ‖f' x‖ * ‖u‖ := (f' x).le_opNorm u
      _ ≤ C * (1 + ‖x‖) ^ k * ‖u‖ := mul_le_mul_of_nonneg_right (hf'b x) (norm_nonneg u)
      _ = ‖u‖ * C * (1 + ‖x‖) ^ k := by ring

end Std

section Pi

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Coordinatewise scaling `z ↦ (√(v i) z i)ᵢ` from `EuclideanSpace ℝ ι` to `ι → ℝ`. -/
def gaussianScale (v : ι → ℝ≥0) : EuclideanSpace ℝ ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i => √(v i : ℝ) • EuclideanSpace.proj i

omit [Fintype ι] in
lemma gaussianScale_apply (v : ι → ℝ≥0) (z : EuclideanSpace ℝ ι) (i : ι) :
    gaussianScale v z i = √(v i : ℝ) * z i := rfl

omit [Fintype ι] in
lemma gaussianScale_single [DecidableEq ι] (v : ι → ℝ≥0) (i : ι) :
    gaussianScale v (EuclideanSpace.single i 1) = √(v i : ℝ) • Pi.single i 1 := by
  funext j
  rw [gaussianScale_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- A product of centred real Gaussians is the image of the standard Gaussian under coordinatewise
scaling. -/
lemma pi_gaussianReal_eq_map (v : ι → ℝ≥0) :
    Measure.pi (fun i => gaussianReal 0 (v i)) =
      (stdGaussian (EuclideanSpace ℝ ι)).map (gaussianScale v) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  have hc : (gaussianScale v ∘ WithLp.toLp 2) = fun (x : ι → ℝ) i => √(v i : ℝ) * x i := rfl
  rw [hc]
  have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun i (t : ℝ) => √(v i : ℝ) * t) (fun i => by fun_prop)
  rw [h]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext; simp

instance isGaussian_pi_gaussianReal (v : ι → ℝ≥0) :
    IsGaussian (Measure.pi fun i => gaussianReal 0 (v i)) := by
  rw [pi_gaussianReal_eq_map]; infer_instance

/-- **Gaussian integration by parts for independent coordinates**: if `x` has independent
`N(0, v j)` coordinates then `E[x i f(x)] = v i E[∂ᵢ f(x)]`, where `∂ᵢ f(x) = f' x (Pi.single i 1)`.
The case `v i = 0` is included. -/
theorem integral_coord_smul_pi_gaussianReal [DecidableEq ι] (v : ι → ℝ≥0) (i : ι)
    {f : (ι → ℝ) → F} {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] F} (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hfi : Integrable f (Measure.pi fun j => gaussianReal 0 (v j)))
    (hxf : Integrable (fun x => x i • f x) (Measure.pi fun j => gaussianReal 0 (v j)))
    (hf' : Integrable (fun x => f' x (Pi.single i 1)) (Measure.pi fun j => gaussianReal 0 (v j))) :
    ∫ x, x i • f x ∂Measure.pi (fun j => gaussianReal 0 (v j)) =
      (v i : ℝ) • ∫ x, f' x (Pi.single i 1) ∂Measure.pi (fun j => gaussianReal 0 (v j)) := by
  rw [pi_gaussianReal_eq_map] at hfi hxf hf' ⊢
  have hT : AEMeasurable (gaussianScale v) (stdGaussian (EuclideanSpace ℝ ι)) := by fun_prop
  rw [integral_map hT hxf.aestronglyMeasurable, integral_map hT hf'.aestronglyMeasurable]
  have hfi₀ := (integrable_map_measure hfi.aestronglyMeasurable hT).1 hfi
  have hxf₀ := (integrable_map_measure hxf.aestronglyMeasurable hT).1 hxf
  have hf'₀ := (integrable_map_measure hf'.aestronglyMeasurable hT).1 hf'
  by_cases hv : v i = 0
  · simp [gaussianScale_apply, hv]
  have hc : √(v i : ℝ) ≠ 0 := by
    rw [Ne, Real.sqrt_eq_zero (NNReal.coe_nonneg _)]; exact_mod_cast hv
  have hH : ∀ z, HasFDerivAt (fun z => f (gaussianScale v z))
      ((f' (gaussianScale v z)).comp (gaussianScale v)) z :=
    fun z => (hf _).comp z (gaussianScale v).hasFDerivAt
  have hxf₁ : Integrable (fun z : EuclideanSpace ℝ ι =>
      ⟪z, EuclideanSpace.single i 1⟫ • f (gaussianScale v z)) (stdGaussian _) := by
    refine (hxf₀.smul (√(v i : ℝ))⁻¹).congr (ae_of_all _ fun z => ?_)
    simp [gaussianScale_apply, EuclideanSpace.inner_single_right, smul_smul, hc]
  have hf'₁ : Integrable (fun z : EuclideanSpace ℝ ι =>
      ((f' (gaussianScale v z)).comp (gaussianScale v)) (EuclideanSpace.single i 1))
      (stdGaussian _) := by
    refine (hf'₀.smul (√(v i : ℝ))).congr (ae_of_all _ fun z => ?_)
    simp [gaussianScale_single]
  have key := integral_inner_smul_stdGaussian (EuclideanSpace.single i 1) hH hfi₀ hxf₁ hf'₁
  calc ∫ z, gaussianScale v z i • f (gaussianScale v z) ∂stdGaussian _
      = √(v i : ℝ) • ∫ z, ⟪z, EuclideanSpace.single i 1⟫ • f (gaussianScale v z)
          ∂stdGaussian _ := by
        rw [← integral_smul]; congr 1; funext z
        simp [gaussianScale_apply, EuclideanSpace.inner_single_right, smul_smul]
    _ = √(v i : ℝ) • ∫ z, ((f' (gaussianScale v z)).comp (gaussianScale v))
          (EuclideanSpace.single i 1) ∂stdGaussian _ := by rw [key]
    _ = (v i : ℝ) • ∫ z, f' (gaussianScale v z) (Pi.single i 1) ∂stdGaussian _ := by
        rw [← integral_smul, ← integral_smul]; congr 1; funext z
        simp [gaussianScale_single, smul_smul, Real.mul_self_sqrt]

/-- Real-valued form: `E[x i f(x)] = v i E[∂ᵢ f(x)]` for independent `N(0, v j)` coordinates. -/
theorem integral_coord_mul_pi_gaussianReal [DecidableEq ι] (v : ι → ℝ≥0) (i : ι)
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ} (hf : ∀ x, HasFDerivAt f (f' x) x)
    (hfi : Integrable f (Measure.pi fun j => gaussianReal 0 (v j)))
    (hxf : Integrable (fun x => x i * f x) (Measure.pi fun j => gaussianReal 0 (v j)))
    (hf' : Integrable (fun x => f' x (Pi.single i 1)) (Measure.pi fun j => gaussianReal 0 (v j))) :
    ∫ x, x i * f x ∂Measure.pi (fun j => gaussianReal 0 (v j)) =
      v i * ∫ x, f' x (Pi.single i 1) ∂Measure.pi (fun j => gaussianReal 0 (v j)) :=
  integral_coord_smul_pi_gaussianReal v i hf hfi hxf hf'

/-- The coordinate identity when `f` and `f'` grow at most polynomially (sup norm on `ι → ℝ`). -/
theorem integral_coord_mul_pi_gaussianReal_of_growth [DecidableEq ι] (v : ι → ℝ≥0) (i : ι)
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ} (hf : ∀ x, HasFDerivAt f (f' x) x)
    {C : ℝ} {k : ℕ} (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf'b : ∀ x, ‖f' x‖ ≤ C * (1 + ‖x‖) ^ k) :
    ∫ x, x i * f x ∂Measure.pi (fun j => gaussianReal 0 (v j)) =
      v i * ∫ x, f' x (Pi.single i 1) ∂Measure.pi (fun j => gaussianReal 0 (v j)) := by
  have hc : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hd : (fun x => f' x (Pi.single i 1)) = fun x => fderiv ℝ f x (Pi.single i 1) :=
    funext fun x => by rw [(hf x).fderiv]
  have hm : AEStronglyMeasurable (fun x => f' x (Pi.single i 1))
      (Measure.pi fun j => gaussianReal 0 (v j)) := by
    rw [hd]; exact (measurable_fderiv_apply_const ℝ f _).aestronglyMeasurable
  refine integral_coord_mul_pi_gaussianReal v i hf
    (integrable_of_norm_le_poly _ hc.aestronglyMeasurable hfb) ?_
    (integrable_of_norm_le_poly _ hm (C := C * ‖(Pi.single i 1 : ι → ℝ)‖) (k := k) fun x => ?_)
  · refine integrable_of_norm_le_poly _ (by fun_prop) (C := C) (k := k + 1) fun x => ?_
    rw [norm_mul]
    calc ‖x i‖ * ‖f x‖ ≤ (1 + ‖x‖) * (C * (1 + ‖x‖) ^ k) :=
          mul_le_mul ((norm_le_pi_norm x i).trans (by linarith [norm_nonneg x])) (hfb x)
            (norm_nonneg _) (by positivity)
      _ = C * (1 + ‖x‖) ^ (k + 1) := by ring
  · calc ‖f' x (Pi.single i 1)‖ ≤ ‖f' x‖ * ‖(Pi.single i 1 : ι → ℝ)‖ := (f' x).le_opNorm _
      _ ≤ C * (1 + ‖x‖) ^ k * ‖(Pi.single i 1 : ι → ℝ)‖ :=
          mul_le_mul_of_nonneg_right (hf'b x) (norm_nonneg _)
      _ = C * ‖(Pi.single i 1 : ι → ℝ)‖ * (1 + ‖x‖) ^ k := by ring

end Pi

section Affine

variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Gaussian integration by parts for an affine image `y = m + A x` of the standard Gaussian, whose
covariance is `A A†`: `E[⟪y - m, w⟫ f(y)] = E[f'(y) (A A† w)]`. -/
theorem integral_inner_sub_smul_map_stdGaussian (A : E →L[ℝ] G) (m w : G) {f : G → F}
    {f' : G → G →L[ℝ] F} (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hfi : Integrable f ((stdGaussian E).map fun x => m + A x))
    (hxf : Integrable (fun y => ⟪y - m, w⟫ • f y) ((stdGaussian E).map fun x => m + A x))
    (hf' : Integrable (fun y => f' y (A (A.adjoint w))) ((stdGaussian E).map fun x => m + A x)) :
    ∫ y, ⟪y - m, w⟫ • f y ∂(stdGaussian E).map (fun x => m + A x) =
      ∫ y, f' y (A (A.adjoint w)) ∂(stdGaussian E).map (fun x => m + A x) := by
  have hT : AEMeasurable (fun x => m + A x) (stdGaussian E) := by fun_prop
  rw [integral_map hT hxf.aestronglyMeasurable, integral_map hT hf'.aestronglyMeasurable]
  have hfi₀ := (integrable_map_measure hfi.aestronglyMeasurable hT).1 hfi
  have hxf₀ := (integrable_map_measure hxf.aestronglyMeasurable hT).1 hxf
  have hf'₀ := (integrable_map_measure hf'.aestronglyMeasurable hT).1 hf'
  have hH : ∀ x, HasFDerivAt (fun x => f (m + A x)) ((f' (m + A x)).comp A) x :=
    fun x => (hf _).comp x (A.hasFDerivAt.const_add m)
  have hxf₁ : Integrable (fun x => ⟪x, A.adjoint w⟫ • f (m + A x)) (stdGaussian E) :=
    hxf₀.congr (ae_of_all _ fun x => by
      simp [Function.comp, ContinuousLinearMap.adjoint_inner_right])
  have key := integral_inner_smul_stdGaussian (A.adjoint w) hH hfi₀ hxf₁ hf'₀
  simpa [ContinuousLinearMap.adjoint_inner_right] using key

/-- Gaussian integration by parts for `multivariateGaussian μ S` with `S` positive semidefinite:
`E[⟪y - μ, w⟫ f(y)] = E[f'(y) (S w)]`; for `w = e_i` this is
`E[(y_i - μ_i) f(y)] = ∑_j S i j E[∂_j f(y)]`. -/
theorem integral_inner_sub_smul_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (w : EuclideanSpace ℝ ι)
    {f : EuclideanSpace ℝ ι → F} {f' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] F}
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hfi : Integrable f (multivariateGaussian μ S))
    (hxf : Integrable (fun y => ⟪y - μ, w⟫ • f y) (multivariateGaussian μ S))
    (hf' : Integrable (fun y => f' y (toEuclideanCLM (𝕜 := ℝ) S w)) (multivariateGaussian μ S)) :
    ∫ y, ⟪y - μ, w⟫ • f y ∂multivariateGaussian μ S =
      ∫ y, f' y (toEuclideanCLM (𝕜 := ℝ) S w) ∂multivariateGaussian μ S := by
  have hA : (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S))
      ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)).adjoint w) = toEuclideanCLM (𝕜 := ℝ) S w := by
    rw [IsSelfAdjoint.adjoint_eq ((CFC.sqrt_nonneg S).isSelfAdjoint.map _),
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  rw [← hA] at hf' ⊢
  exact integral_inner_sub_smul_map_stdGaussian _ μ w hf hfi hxf hf'

end Affine
end

end TheoremOS.Probability
