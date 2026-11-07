import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PlanarAnderson

abbrev Site := ℤ × ℤ
abbrev Configuration := Site → ℝ
abbrev Hilbert := lp (fun _ : Site => ℂ) 2

def disorderLaw (h : ℝ) : Measure Configuration :=
  Measure.infinitePi (fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h))

def IsAndersonOperator (v : Configuration) (H : Hilbert →L[ℂ] Hilbert) : Prop :=
  ∀ (u : Hilbert) (x : Site),
    (H u) x = u (x.1 + 1, x.2) + u (x.1 - 1, x.2) +
      u (x.1, x.2 + 1) + u (x.1, x.2 - 1) + (v x : ℂ) * u x

def spectralInterval (h : ℝ) : Set ℂ :=
  {z | z.im = 0 ∧ -4 - h ≤ z.re ∧ z.re ≤ 4 + h}

theorem andersonOperator_unique {v : Configuration} {H₁ H₂ : Hilbert →L[ℂ] Hilbert}
    (h₁ : IsAndersonOperator v H₁) (h₂ : IsAndersonOperator v H₂) : H₁ = H₂ := by
  ext u x
  rw [h₁ u x, h₂ u x]
theorem ae_bounded {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∀ x : Site, |v x| ≤ h := by
  classical
  let μ : Site → Measure ℝ := fun _ =>
    ProbabilityTheory.cond volume (Set.Icc (-h) h)
  have hprob : ∀ i : Site, IsProbabilityMeasure (μ i) := fun _ => by
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
  have hcoord : ∀ x : Site, ∀ᵐ v ∂disorderLaw h, v x ∈ Set.Icc (-h) h := by
    intro x
    change ∀ᵐ v ∂Measure.infinitePi μ, v x ∈ Set.Icc (-h) h
    exact (measurePreserving_eval_infinitePi (μ := μ) (hμ := hprob) x).quasiMeasurePreserving.ae
      (ProbabilityTheory.ae_cond_mem measurableSet_Icc)
  filter_upwards [ae_all_iff.2 hcoord] with v hv x
  exact abs_le.mpr (Set.mem_Icc.mp (hv x))
lemma memℓp_shift (a : Site) (u : Hilbert) :
    Memℓp (fun x : Site => (u : Site → ℂ) (x + a)) 2 := by
  apply memℓp_gen
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h : Summable fun i : Site => ‖(u : Site → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp u).summable hp
  have h2 := (Equiv.summable_iff (Equiv.addRight a)).2 h
  convert h2 using 1
  ext x
  rfl
def shiftLp (a : Site) (u : Hilbert) : Hilbert :=
  ⟨fun x : Site => (u : Site → ℂ) (x + a), memℓp_shift a u⟩
lemma shiftLp_coe (a : Site) (u : Hilbert) (x : Site) :
    (shiftLp a u : Site → ℂ) x = (u : Site → ℂ) (x + a) := rfl
lemma shiftLp_add (a : Site) (u w : Hilbert) :
    shiftLp a (u + w) = shiftLp a u + shiftLp a w := by
  ext x
  simp only [shiftLp_coe, lp.coeFn_add, Pi.add_apply]
lemma shiftLp_smul (a : Site) (c : ℂ) (u : Hilbert) : shiftLp a (c • u) = c • shiftLp a u := by
  ext x
  simp only [shiftLp_coe, lp.coeFn_smul, Pi.smul_apply]
lemma norm_shiftLp (a : Site) (u : Hilbert) : ‖shiftLp a u‖ = ‖u‖ := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have e : (∑' i : Site, ‖(u : Site → ℂ) ((Equiv.addRight a) i)‖ ^ (2 : ℝ≥0∞).toReal)
      = ∑' i : Site, ‖(u : Site → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    Equiv.tsum_eq (Equiv.addRight a) (fun i : Site => ‖(u : Site → ℂ) i‖ ^ (2:ℝ≥0∞).toReal)
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  simp only [shiftLp]
  congr 1
noncomputable def shiftCLM (a : Site) : Hilbert →L[ℂ] Hilbert :=
  LinearMap.mkContinuous
    { toFun := shiftLp a
      map_add' := shiftLp_add a
      map_smul' := fun c u => shiftLp_smul a c u }
    1 (fun u => by
      change ‖shiftLp a u‖ ≤ 1 * ‖u‖
      rw [norm_shiftLp, one_mul])
lemma shiftCLM_apply (a : Site) (u : Hilbert) : shiftCLM a u = shiftLp a u := rfl
lemma norm_shiftCLM_le (a : Site) : ‖shiftCLM a‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
  change ‖shiftLp a u‖ ≤ 1 * ‖u‖
  rw [norm_shiftLp, one_mul]
lemma memℓp_mul {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) (u : Hilbert) :
    Memℓp (fun x : Site => (v x : ℂ) * (u : Site → ℂ) x) 2 := by
  have hh : 0 ≤ h := le_trans (abs_nonneg (v 0)) (hv 0)
  apply memℓp_gen
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have hb : Summable fun i : Site => ‖(u : Site → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp u).summable hp
  have hsum : Summable fun i : Site => (h * h) * ‖(u : Site → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal :=
    hb.mul_left (h * h)
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hsum
  have h1 : ‖((v i : ℂ) * (u : Site → ℂ) i)‖ = |v i| * ‖(u : Site → ℂ) i‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h4 : |v i| * ‖(u : Site → ℂ) i‖ ≤ h * ‖(u : Site → ℂ) i‖ :=
    mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
  calc ‖((v i : ℂ) * (u : Site → ℂ) i)‖ ^ (2 : ℝ≥0∞).toReal
      = (|v i| * ‖(u : Site → ℂ) i‖) ^ 2 := by rw [h1]; norm_num
    _ ≤ (h * ‖(u : Site → ℂ) i‖) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
    _ = (h * h) * ‖(u : Site → ℂ) i‖ ^ (2 : ℝ≥0∞).toReal := by ring_nf; norm_num
def mulLp {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) (u : Hilbert) : Hilbert :=
  ⟨fun x : Site => (v x : ℂ) * (u : Site → ℂ) x, memℓp_mul hv u⟩
lemma mulLp_coe {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h)
    (u : Hilbert) (x : Site) :
    (mulLp hv u : Site → ℂ) x = (v x : ℂ) * (u : Site → ℂ) x := rfl
lemma mulLp_add {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) (u w : Hilbert) :
    mulLp hv (u + w) = mulLp hv u + mulLp hv w := by
  ext x
  simp only [mulLp_coe, lp.coeFn_add, Pi.add_apply, mul_add]
lemma mulLp_smul {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) (c : ℂ)
    (u : Hilbert) : mulLp hv (c • u) = c • mulLp hv u := by
  ext x
  simp only [mulLp_coe, lp.coeFn_smul, Pi.smul_apply]
  ring
lemma norm_mulLp_le {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) (u : Hilbert) :
    ‖mulLp hv u‖ ≤ h * ‖u‖ := by
  have hh : 0 ≤ h := le_trans (abs_nonneg (v 0)) (hv 0)
  have hmono : ‖mulLp hv u‖ ≤ ‖(h : ℝ) • u‖ := by
    refine lp.norm_mono (p := 2) (E := fun _ : Site => ℂ) (F := fun _ : Site => ℂ)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (x := mulLp hv u) (y := (h : ℝ) • u) (fun i => ?_)
    rw [mulLp_coe, lp.coeFn_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
  calc ‖mulLp hv u‖ ≤ ‖(h : ℝ) • u‖ := hmono
    _ = h * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
noncomputable def mulCLM {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) :
    Hilbert →L[ℂ] Hilbert :=
  LinearMap.mkContinuous
    { toFun := mulLp hv
      map_add' := mulLp_add hv
      map_smul' := fun c u => mulLp_smul hv c u }
    h (fun u => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact norm_mulLp_le hv u)
lemma mulCLM_apply {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h)
    (u : Hilbert) : mulCLM hv u = mulLp hv u := rfl
lemma norm_mulCLM_le {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) :
    ‖mulCLM hv‖ ≤ h := by
  have hh : 0 ≤ h := le_trans (abs_nonneg (v 0)) (hv 0)
  exact LinearMap.mkContinuous_norm_le _ hh (fun u => norm_mulLp_le hv u)
lemma mulCLM_coe {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h)
    (u : Hilbert) (x : Site) :
    (mulCLM hv u : Site → ℂ) x = (v x : ℂ) * (u : Site → ℂ) x := rfl
lemma mulCLM_isSelfAdjoint {h : ℝ} {v : Configuration} (hv : ∀ x : Site, |v x| ≤ h) :
    IsSelfAdjoint (mulCLM hv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u w
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  show inner ℂ ((v x : ℂ) * (u : Site → ℂ) x) ((w : Site → ℂ) x)
    = inner ℂ ((u : Site → ℂ) x) ((v x : ℂ) * (w : Site → ℂ) x)
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring
lemma inner_shiftLp (a : Site) (u w : Hilbert) :
    inner ℂ (shiftLp a u) w = inner ℂ u (shiftLp (-a) w) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [shiftLp_coe]
  rw [← Equiv.tsum_eq (Equiv.addRight a)
    (fun y : Site => inner ℂ ((u : Site → ℂ) y) ((w : Site → ℂ) (y + -a)))]
  apply tsum_congr
  intro x
  simp
lemma shift_add_neg_isSelfAdjoint (a : Site) :
    IsSelfAdjoint (shiftCLM a + shiftCLM (-a)) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u w
  change inner ℂ ((shiftCLM a + shiftCLM (-a)) u) w
    = inner ℂ u ((shiftCLM a + shiftCLM (-a)) w)
  rw [add_apply, add_apply, inner_add_left, inner_add_right]
  simp only [shiftCLM_apply]
  rw [inner_shiftLp a, inner_shiftLp (-a), neg_neg]
  exact add_comm _ _
lemma isSelfAdjoint_add_op {A B : Hilbert →L[ℂ] Hilbert} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) : IsSelfAdjoint (A + B) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hA hB ⊢
  intro x y
  have h1 : inner ℂ (A x) y = inner ℂ x (A y) := hA x y
  have h2 : inner ℂ (B x) y = inner ℂ x (B y) := hB x y
  show inner ℂ (A x + B x) y = inner ℂ x (A y + B y)
  rw [inner_add_left, inner_add_right, h1, h2]
noncomputable def adjacencyCLM : Hilbert →L[ℂ] Hilbert :=
  (shiftCLM (1, 0) + shiftCLM (-1, 0)) + (shiftCLM (0, 1) + shiftCLM (0, -1))
lemma adjacencyCLM_isSelfAdjoint : IsSelfAdjoint adjacencyCLM := by
  have h1 : IsSelfAdjoint (shiftCLM (1, 0) + shiftCLM (-1, 0)) :=
    shift_add_neg_isSelfAdjoint (1, 0)
  have h2 : IsSelfAdjoint (shiftCLM (0, 1) + shiftCLM (0, -1)) :=
    shift_add_neg_isSelfAdjoint (0, 1)
  exact isSelfAdjoint_add_op h1 h2
lemma norm_adjacencyCLM_le : ‖adjacencyCLM‖ ≤ 4 := by
  have h1 := norm_shiftCLM_le (1, 0)
  have h2 := norm_shiftCLM_le (-1, 0)
  have h3 := norm_shiftCLM_le (0, 1)
  have h4 := norm_shiftCLM_le (0, -1)
  have h5 := norm_add_le (shiftCLM (1, 0)) (shiftCLM (-1, 0))
  have h6 := norm_add_le (shiftCLM (0, 1)) (shiftCLM (0, -1))
  have h7 := norm_add_le (shiftCLM (1, 0) + shiftCLM (-1, 0))
    (shiftCLM (0, 1) + shiftCLM (0, -1))
  rw [adjacencyCLM]
  linarith
lemma adjacencyCLM_apply (u : Hilbert) (x : Site) :
    (adjacencyCLM u : Site → ℂ) x =
      (u : Site → ℂ) (x.1 + 1, x.2) + (u : Site → ℂ) (x.1 - 1, x.2) +
        (u : Site → ℂ) (x.1, x.2 + 1) + (u : Site → ℂ) (x.1, x.2 - 1) := by
  have e1 : x + (1, 0) = (x.1 + 1, x.2) := by ext <;> simp
  have e2 : x + (-1, 0) = (x.1 - 1, x.2) := by ext <;> simp [sub_eq_add_neg]
  have e3 : x + (0, 1) = (x.1, x.2 + 1) := by ext <;> simp
  have e4 : x + (0, -1) = (x.1, x.2 - 1) := by ext <;> simp [sub_eq_add_neg]
  have hcoe : (adjacencyCLM u : Site → ℂ) =
      ((shiftLp (1, 0) u : Site → ℂ) + (shiftLp (-1, 0) u : Site → ℂ)) +
        ((shiftLp (0, 1) u : Site → ℂ) + (shiftLp (0, -1) u : Site → ℂ)) := by
    rw [adjacencyCLM, add_apply, add_apply, add_apply, lp.coeFn_add, lp.coeFn_add, lp.coeFn_add]
    rfl
  rw [hcoe]
  simp only [Pi.add_apply, shiftLp_coe, e1, e2, e3, e4]
  abel
theorem anderson_operator_exists_selfAdjoint {h : ℝ} (v : Configuration)
    (hv : ∀ x : Site, |v x| ≤ h) :
    ∃ H : Hilbert →L[ℂ] Hilbert, IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ ‖H‖ ≤ 4 + h := by
  refine ⟨adjacencyCLM + mulCLM hv, ?_, ?_, ?_⟩
  · intro u x
    have hcoe : ((adjacencyCLM + mulCLM hv) u : Site → ℂ) x
        = (adjacencyCLM u : Site → ℂ) x + (mulCLM hv u : Site → ℂ) x := by
      rw [add_apply, lp.coeFn_add]
      rfl
    rw [hcoe, adjacencyCLM_apply, mulCLM_coe]
  · exact isSelfAdjoint_add_op adjacencyCLM_isSelfAdjoint (mulCLM_isSelfAdjoint hv)
  · have h1 := norm_add_le adjacencyCLM (mulCLM hv)
    have h2 := norm_adjacencyCLM_le
    have h3 := norm_mulCLM_le hv
    linarith
theorem spectrum_subset_spectralInterval_of_norm_le {h : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hsa : IsSelfAdjoint H) (hnorm : ‖H‖ ≤ 4 + h) : spectrum ℂ H ⊆ spectralInterval h := by
  intro z hz
  have hzre : z = (z.re : ℂ) := hsa.mem_spectrum_eq_re hz
  have hzball : z ∈ Metric.closedBall (0 : ℂ) (‖H‖ * ‖(1 : Hilbert →L[ℂ] Hilbert)‖) :=
    spectrum.subset_closedBall_norm_mul H hz
  have hznorm : ‖z‖ ≤ ‖H‖ * ‖(1 : Hilbert →L[ℂ] Hilbert)‖ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  have hzH : ‖z‖ ≤ ‖H‖ := by
    calc ‖z‖ ≤ ‖H‖ * ‖(1 : Hilbert →L[ℂ] Hilbert)‖ := hznorm
      _ ≤ ‖H‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = ‖H‖ := mul_one _
  have hzle : ‖z‖ ≤ 4 + h := le_trans hzH hnorm
  have hre_le : |z.re| ≤ 4 + h := by
    have hle : ‖z.re‖ ≤ ‖z‖ := Complex.abs_re_le_norm z
    simpa [Real.norm_eq_abs] using le_trans hle hzle
  have hb := abs_le.mp hre_le
  exact ⟨by rw [hzre]; simp, by linarith [hb.1], by linarith [hb.2]⟩
theorem norm_le_of_isAndersonOperator {h : ℝ} {v : Configuration}
    {H H₀ : Hilbert →L[ℂ] Hilbert} (hop : IsAndersonOperator v H)
    (hop₀ : IsAndersonOperator v H₀) (hnorm₀ : ‖H₀‖ ≤ 4 + h) : ‖H‖ ≤ 4 + h := by
  have huniq : H = H₀ := by
    ext u x
    rw [hop u x, hop₀ u x]
  rw [huniq]
  exact hnorm₀
theorem spectrum_subset_spectralInterval_of_bounded_potential {h : ℝ} {v : Configuration}
    {H : Hilbert →L[ℂ] Hilbert} (hop : IsAndersonOperator v H) (hsa : IsSelfAdjoint H)
    {H₀ : Hilbert →L[ℂ] Hilbert} (hop₀ : IsAndersonOperator v H₀) (hnorm₀ : ‖H₀‖ ≤ 4 + h) :
    spectrum ℂ H ⊆ spectralInterval h :=
  spectrum_subset_spectralInterval_of_norm_le hsa (norm_le_of_isAndersonOperator hop hop₀ hnorm₀)
theorem spectrum_subset_spectralInterval_of_exists {h : ℝ} {v : Configuration}
    {H : Hilbert →L[ℂ] Hilbert} (hop : IsAndersonOperator v H) (hsa : IsSelfAdjoint H)
    (hex : ∃ H₀ : Hilbert →L[ℂ] Hilbert, IsAndersonOperator v H₀ ∧ ‖H₀‖ ≤ 4 + h) :
    spectrum ℂ H ⊆ spectralInterval h := by
  obtain ⟨H₀, hop₀, hnorm₀⟩ := hex
  exact spectrum_subset_spectralInterval_of_bounded_potential hop hsa hop₀ hnorm₀
theorem anderson_spectrum_subset {h : ℝ} (v : Configuration) (H : Hilbert →L[ℂ] Hilbert)
    (hv : ∀ x : Site, |v x| ≤ h) (hop : IsAndersonOperator v H) (hsa : IsSelfAdjoint H) :
    spectrum ℂ H ⊆ spectralInterval h := by
  obtain ⟨H₀, hop₀, -, hnorm₀⟩ := anderson_operator_exists_selfAdjoint (h := h) v hv
  exact spectrum_subset_spectralInterval_of_exists hop hsa ⟨H₀, hop₀, hnorm₀⟩
theorem approx_eigenvalue_mem_spectrum {T : Hilbert →L[ℂ] Hilbert} {z : ℂ}
    (h : ∃ u : ℕ → Hilbert, (∀ n, ‖u n‖ = 1) ∧
      Filter.Tendsto (fun n => ‖(T - z • (1 : Hilbert →L[ℂ] Hilbert)) (u n)‖) Filter.atTop (nhds 0)) :
    z ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨u, hu1, hu2⟩ := h
  set A : Hilbert →L[ℂ] Hilbert := (algebraMap ℂ (Hilbert →L[ℂ] Hilbert)) z - T with hA
  have hneg : A = -(T - z • (1 : Hilbert →L[ℂ] Hilbert)) := by
    rw [hA, Algebra.algebraMap_eq_smul_one]
    abel
  have hnorm : ∀ n, ‖A (u n)‖ = ‖(T - z • (1 : Hilbert →L[ℂ] Hilbert)) (u n)‖ := by
    intro n
    rw [hneg, neg_apply, norm_neg]
  set B : Hilbert →L[ℂ] Hilbert := ↑((hunit.unit)⁻¹) with hB
  have hunit_spec : (↑hunit.unit : Hilbert →L[ℂ] Hilbert) = A := IsUnit.unit_spec hunit
  have hmulBA : B * A = 1 := by
    rw [hB]
    calc (↑hunit.unit⁻¹ : Hilbert →L[ℂ] Hilbert) * A
        = ↑hunit.unit⁻¹ * ↑hunit.unit := by rw [hunit_spec]
      _ = 1 := Units.inv_mul hunit.unit
  have hle : ∀ n, (1:ℝ) ≤ ‖B‖ * ‖A (u n)‖ := by
    intro n
    have happ : B (A (u n)) = u n := by
      have := congrArg (fun f : Hilbert →L[ℂ] Hilbert => f (u n)) hmulBA
      simpa using this
    calc (1:ℝ) = ‖u n‖ := by rw [hu1 n]
      _ = ‖B (A (u n))‖ := by rw [happ]
      _ ≤ ‖B‖ * ‖A (u n)‖ := ContinuousLinearMap.le_opNorm _ _
  have hzero : Filter.Tendsto (fun n => ‖B‖ * ‖A (u n)‖) Filter.atTop (nhds (‖B‖ * 0)) :=
    Filter.Tendsto.const_mul _ (hu2.congr (fun n => (hnorm n).symm))
  have hcontra := le_of_tendsto_of_tendsto tendsto_const_nhds hzero (Filter.Eventually.of_forall hle)
  simp only [mul_zero] at hcontra
  linarith [norm_nonneg B]
lemma natAbs_le_iff (n : ℕ) (y : ℤ) :
    y.natAbs ≤ n ↔ y ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc, ← abs_le, ← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
lemma mem_block_iff (a : Site) (n : ℕ) (x : Site) :
    (x ∈ Finset.Icc (a.1 - n) (a.1 + n) ×ˢ Finset.Icc (a.2 - n) (a.2 + n)) ↔
      (x.1 - a.1).natAbs ≤ n ∧ (x.2 - a.2).natAbs ≤ n := by
  simp only [Finset.mem_product, Finset.mem_Icc, natAbs_le_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
lemma card_block (n : ℕ) :
    (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).card
      = (2 * n + 1) ^ 2 := by
  rw [Finset.card_product, Int.card_Icc]
  have : ((n : ℤ) + 1 - (-(n : ℤ))).toNat = 2 * n + 1 := by
    rw [show (n : ℤ) + 1 - (-(n : ℤ)) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring]
    exact Int.toNat_natCast (2 * n + 1)
  rw [this, sq]
def block (N : ℕ) (i : ℕ) : Finset Site :=
  Finset.Icc (((i * (2 * N + 2) : ℕ) : ℤ) - (N : ℤ))
      (((i * (2 * N + 2) : ℕ) : ℤ) + (N : ℤ)) ×ˢ
    Finset.Icc (-(N : ℤ)) (N : ℤ)
lemma block_card (N i : ℕ) : (block N i).card = (2 * N + 1) ^ 2 := by
  unfold block
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h1 : ((((i * (2 * N + 2) : ℕ) : ℤ) + (N : ℤ)) + 1 -
      (((i * (2 * N + 2) : ℕ) : ℤ) - (N : ℤ))).toNat = 2 * N + 1 := by
    rw [show (((i * (2 * N + 2) : ℕ) : ℤ) + (N : ℤ)) + 1 -
        (((i * (2 * N + 2) : ℕ) : ℤ) - (N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) by
      push_cast; ring]
    exact Int.toNat_natCast (2 * N + 1)
  have h2 : (((N : ℤ)) + 1 - (-(N : ℤ))).toNat = 2 * N + 1 := by
    rw [show ((N : ℤ)) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) by
      push_cast; ring]
    exact Int.toNat_natCast (2 * N + 1)
  rw [h1, h2, sq]
lemma block_disjoint (N i j : ℕ) (hij : i ≠ j) : Disjoint (block N i) (block N j) := by
  unfold block
  rw [Finset.disjoint_product]
  left
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_Icc] at hx hx'
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : (i * (2 * N + 2) : ℕ) + (2 * N + 2) ≤ j * (2 * N + 2) := by
      have : i + 1 ≤ j := Nat.succ_le_of_lt hlt
      calc i * (2 * N + 2) + (2 * N + 2) = (i + 1) * (2 * N + 2) := by ring
        _ ≤ j * (2 * N + 2) := Nat.mul_le_mul_right _ this
    have hstep' : ((i * (2 * N + 2) : ℕ) : ℤ) + ((2 * N + 2 : ℕ) : ℤ)
        ≤ (j * (2 * N + 2) : ℕ) := by exact_mod_cast hstep
    have hstep'' : ((i * (2 * N + 2) : ℕ) : ℤ) + (2 * (N : ℤ) + 2)
        ≤ (j * (2 * N + 2) : ℕ) := by
      simpa using hstep'
    linarith
  · have hstep : (j * (2 * N + 2) : ℕ) + (2 * N + 2) ≤ i * (2 * N + 2) := by
      have : j + 1 ≤ i := Nat.succ_le_of_lt hgt
      calc j * (2 * N + 2) + (2 * N + 2) = (j + 1) * (2 * N + 2) := by ring
        _ ≤ i * (2 * N + 2) := Nat.mul_le_mul_right _ this
    have hstep' : ((j * (2 * N + 2) : ℕ) : ℤ) + ((2 * N + 2 : ℕ) : ℤ)
        ≤ (i * (2 * N + 2) : ℕ) := by exact_mod_cast hstep
    have hstep'' : ((j * (2 * N + 2) : ℕ) : ℤ) + (2 * (N : ℤ) + 2)
        ≤ (i * (2 * N + 2) : ℕ) := by
      simpa using hstep'
    linarith
lemma card_biUnion_blocks (N : ℕ) (s : Finset ℕ) :
    (s.biUnion (block N)).card = s.card * (2 * N + 1) ^ 2 := by
  rw [Finset.card_biUnion]
  · have hsum : (∑ u ∈ s, (block N u).card) = ∑ _u ∈ s, (2 * N + 1) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact block_card N u
    rw [hsum, Finset.sum_const, smul_eq_mul, mul_comm]
  · intro i hi j hj hij
    exact block_disjoint N i j hij
lemma biInter_cylinder (N : ℕ) (c ε : ℝ) (s : Finset ℕ) :
    (⋂ i ∈ s, Set.pi (↑(block N i) : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε)))
      = Set.pi (↑(s.biUnion (block N)) : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε)) := by
  ext v
  simp only [Set.mem_iInter, Set.mem_pi, Finset.mem_coe, Finset.mem_biUnion]
  constructor
  · intro hv x hx
    obtain ⟨i, his, hxi⟩ := hx
    exact hv i his x hxi
  · intro hv i his x hxi
    exact hv x ⟨i, his, hxi⟩
lemma block_mem_iff (N : ℕ) (i : ℕ) (x : Site) :
    x ∈ block N i ↔ (x.1 - ((i * (2 * N + 2) : ℕ) : ℤ)).natAbs ≤ N ∧
      (x.2 - 0).natAbs ≤ N := by
  unfold block
  simp only [Finset.mem_product, Finset.mem_Icc, natAbs_le_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
lemma cond_Ioo_pos {h : ℝ} (hh : 0 < h) {c : ℝ} (hc : c ∈ Set.Icc (-h) h)
    {ε : ℝ} (hε : 0 < ε) :
    0 < ProbabilityTheory.cond volume (Set.Icc (-h) h) (Set.Ioo (c - ε) (c + ε)) := by
  have hc1 : -h ≤ c := hc.1
  have hc2 : c ≤ h := hc.2
  let s : Set ℝ := Set.Icc (-h) h
  let t : Set ℝ := Set.Ioo (c - ε) (c + ε)
  have hms : MeasurableSet s := measurableSet_Icc
  have hsub : Set.Ioo (max (-h) (c - ε)) (min h (c + ε)) ⊆ s ∩ t := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    constructor
    · rw [Set.mem_Icc]
      constructor
      · linarith [hx.1, le_max_left (-h) (c - ε)]
      · linarith [hx.2, min_le_left h (c + ε)]
    · rw [Set.mem_Ioo]
      constructor
      · linarith [hx.1, le_max_right (-h) (c - ε)]
      · linarith [hx.2, min_le_right h (c + ε)]
  have hlt : max (-h) (c - ε) < min h (c + ε) := by
    rw [max_lt_iff]
    constructor
    · exact lt_min_iff.mpr ⟨by linarith, by linarith⟩
    · exact lt_min_iff.mpr ⟨by linarith, by linarith⟩
  have hpos : 0 < volume (Set.Ioo (max (-h) (c - ε)) (min h (c + ε))) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlt)
  have hne : volume (s ∩ t) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hpos (measure_mono hsub))
  have hstop : volume s ≠ ∞ := by
    rw [show s = Set.Icc (-h) h from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  rw [ProbabilityTheory.cond_apply hms volume t]
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hstop) hne
lemma cylinderProb {h : ℝ} (hh : 0 < h) (c ε : ℝ) (B : Finset Site) :
    disorderLaw h (Set.pi (↑B : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε)))
      = (ProbabilityTheory.cond volume (Set.Icc (-h) h)
          (Set.Ioo (c - ε) (c + ε))) ^ B.card := by
  let μ : Site → Measure ℝ := fun _ => ProbabilityTheory.cond volume (Set.Icc (-h) h)
  have hprob : ∀ i : Site, IsProbabilityMeasure (μ i) := fun _ => by
    apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    · rw [Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top
  change Measure.infinitePi μ (Set.pi (↑B : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε)))
      = (ProbabilityTheory.cond volume (Set.Icc (-h) h)
          (Set.Ioo (c - ε) (c + ε))) ^ B.card
  rw [Measure.infinitePi_pi (μ := μ) (hμ := hprob) (s := B)
    (t := fun _ => Set.Ioo (c - ε) (c + ε)) (by intro i hi; exact measurableSet_Ioo)]
  change (∏ i ∈ B, (fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h)
      (Set.Ioo (c - ε) (c + ε))) i) = _
  rw [Finset.prod_const]
lemma indep_cylinders {h : ℝ} (hh : 0 < h) (c ε : ℝ) (N : ℕ) :
    ProbabilityTheory.iIndepSet (fun i : ℕ => Set.pi (↑(block N i) : Set Site)
      (fun _ => Set.Ioo (c - ε) (c + ε))) (disorderLaw h) := by
  apply (ProbabilityTheory.iIndepSet_iff_meas_biInter (f := fun i : ℕ =>
    Set.pi (↑(block N i) : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε)))
    (μ := disorderLaw h) (fun i => ?_)).2
  · intro s
    rw [biInter_cylinder, cylinderProb hh, card_biUnion_blocks]
    have hprod : (∏ i ∈ s, disorderLaw h (Set.pi (↑(block N i) : Set Site)
        (fun _ => Set.Ioo (c - ε) (c + ε))))
        = ∏ _i ∈ s, (ProbabilityTheory.cond volume (Set.Icc (-h) h)
            (Set.Ioo (c - ε) (c + ε))) ^ (2 * N + 1) ^ 2 := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [cylinderProb hh, block_card]
    rw [hprod, Finset.prod_const]
    rw [show s.card * (2 * N + 1) ^ 2 = ((2 * N + 1) ^ 2) * s.card by ring]
    rw [pow_mul]
  · exact MeasurableSet.pi (Finset.countable_toSet _) (fun i hi => measurableSet_Ioo)
theorem constant_block_occurrence {h : ℝ} (hh : 0 < h) :
    ∀ c ∈ Set.Icc (-h) h, ∀ ε > 0, ∀ N : ℕ,
      ∀ᵐ v ∂disorderLaw h, ∃ (a : Site) (n : ℕ), N ≤ n ∧ ∀ x : Site,
        (x.1 - a.1).natAbs ≤ n → (x.2 - a.2).natAbs ≤ n → |v x - c| < ε := by
  intro c hc ε hε N
  let p : ℝ≥0∞ := ProbabilityTheory.cond volume (Set.Icc (-h) h) (Set.Ioo (c - ε) (c + ε))
  let E : ℕ → Set Configuration := fun i =>
    Set.pi (↑(block N i) : Set Site) (fun _ => Set.Ioo (c - ε) (c + ε))
  have hp : 0 < p := cond_Ioo_pos hh hc hε
  have hpne : p ≠ 0 := ne_of_gt hp
  have hEmeas : ∀ i, MeasurableSet (E i) := fun i =>
    MeasurableSet.pi (Finset.countable_toSet _) (fun _ _ => measurableSet_Ioo)
  have hindep : ProbabilityTheory.iIndepSet E (disorderLaw h) :=
    indep_cylinders hh c ε N
  have hconst : ∀ i : ℕ, disorderLaw h (E i) = p ^ ((2 * N + 1) ^ 2) := by
    intro i
    exact cylinderProb hh c ε (block N i) |>.trans (by rw [block_card])
  have hsum : (∑' i : ℕ, disorderLaw h (E i)) = ∞ := by
    simp_rw [hconst]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero _ hpne)
  have hlim : disorderLaw h (Filter.limsup E Filter.atTop) = 1 :=
    ProbabilityTheory.measure_limsup_eq_one hEmeas hindep hsum
  have hlimmeas : MeasurableSet (Filter.limsup E Filter.atTop) :=
    MeasurableSet.measurableSet_limsup hEmeas
  have huniv : disorderLaw h Set.univ = 1 := by
    have hempty := cylinderProb hh c ε (∅ : Finset Site)
    simpa using hempty
  have hcompl0 : disorderLaw h (Filter.limsup E Filter.atTop)ᶜ = 0 := by
    rw [MeasureTheory.measure_compl hlimmeas]
    · rw [hlim, huniv, tsub_self]
    · rw [hlim]; exact ENNReal.one_ne_top
  have hlim_ae : ∀ᵐ v ∂disorderLaw h, v ∈ Filter.limsup E Filter.atTop := by
    rw [MeasureTheory.ae_iff]
    exact hcompl0
  filter_upwards [hlim_ae] with v hv
  rw [Filter.mem_limsup_iff_frequently_mem] at hv
  obtain ⟨i, hi⟩ := Filter.Frequently.exists hv
  refine ⟨(((i * (2 * N + 2) : ℕ) : ℤ), 0), N, le_rfl, ?_⟩
  intro x hx1 hx2
  have hxblock : x ∈ block N i := by
    rw [block_mem_iff]
    exact ⟨hx1, hx2⟩
  have hmem : v x ∈ Set.Ioo (c - ε) (c + ε) := Set.mem_pi.mp hi x hxblock
  rw [Set.mem_Ioo] at hmem
  exact abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
def phase (α β : ℝ) (x : Site) : ℂ :=
  Complex.exp (((α * (x.1 : ℝ) + β * (x.2 : ℝ)) : ℝ) * Complex.I)
lemma norm_phase (α β : ℝ) (x : Site) : ‖phase α β x‖ = 1 := by
  rw [phase, Complex.norm_exp_ofReal_mul_I]
lemma exp_I_add_neg (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp ((-(θ : ℂ)) * Complex.I)
      = ((2 * Real.cos θ : ℝ) : ℂ) := by
  have h1 : Complex.exp ((θ : ℂ) * Complex.I)
      = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have h2 : Complex.exp ((-(θ : ℂ)) * Complex.I)
      = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    rw [show (-(θ : ℂ)) = ((-θ : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    simp only [Complex.ofReal_neg]
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  push_cast
  ring
lemma phase_e1 (α β : ℝ) (x : Site) :
    phase α β (x.1 + 1, x.2) = Complex.exp ((α : ℂ) * Complex.I) * phase α β x := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_m1 (α β : ℝ) (x : Site) :
    phase α β (x.1 - 1, x.2) = Complex.exp ((-(α : ℂ)) * Complex.I) * phase α β x := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_e2 (α β : ℝ) (x : Site) :
    phase α β (x.1, x.2 + 1) = Complex.exp ((β : ℂ) * Complex.I) * phase α β x := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_m2 (α β : ℝ) (x : Site) :
    phase α β (x.1, x.2 - 1) = Complex.exp ((-(β : ℂ)) * Complex.I) * phase α β x := by
  rw [phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring
lemma phase_neighbors (α β : ℝ) (x : Site) :
    phase α β (x.1 + 1, x.2) + phase α β (x.1 - 1, x.2) +
      phase α β (x.1, x.2 + 1) + phase α β (x.1, x.2 - 1) =
    ((2 * Real.cos α + 2 * Real.cos β : ℝ) : ℂ) * phase α β x := by
  rw [phase_e1, phase_m1, phase_e2, phase_m2]
  have h1 := exp_I_add_neg α
  have h2 := exp_I_add_neg β
  calc Complex.exp ((α : ℂ) * Complex.I) * phase α β x +
        Complex.exp ((-(α : ℂ)) * Complex.I) * phase α β x +
        Complex.exp ((β : ℂ) * Complex.I) * phase α β x +
        Complex.exp ((-(β : ℂ)) * Complex.I) * phase α β x
      = (Complex.exp ((α : ℂ) * Complex.I) + Complex.exp ((-(α : ℂ)) * Complex.I)) *
          phase α β x +
        (Complex.exp ((β : ℂ) * Complex.I) + Complex.exp ((-(β : ℂ)) * Complex.I)) *
          phase α β x := by
        ring
    _ = ((2 * Real.cos α : ℝ) : ℂ) * phase α β x +
        ((2 * Real.cos β : ℝ) : ℂ) * phase α β x := by rw [h1, h2]
    _ = ((2 * Real.cos α + 2 * Real.cos β : ℝ) : ℂ) * phase α β x := by
        push_cast; ring
def boxF (n : ℕ) : Finset Site :=
  Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)
lemma mem_boxF {n : ℕ} {x : Site} :
    x ∈ boxF n ↔ -(n : ℤ) ≤ x.1 ∧ x.1 ≤ (n : ℤ) ∧ -(n : ℤ) ≤ x.2 ∧ x.2 ≤ (n : ℤ) := by
  simp [boxF, Finset.mem_product, Finset.mem_Icc, and_assoc]
lemma card_Icc_int (n : ℕ) : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
  rw [Int.card_Icc]
  have h : ((n : ℤ) + 1 - (-(n : ℤ))) = ((2 * n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]
lemma card_boxF (n : ℕ) : (boxF n).card = (2 * n + 1) ^ 2 := by
  rw [boxF, Finset.card_product, card_Icc_int]; ring
lemma card_faceH (n : ℕ) (c : ℤ) :
    ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ ({(c)} : Finset ℤ)).card = 2 * n + 1 := by
  rw [Finset.card_product, Finset.card_singleton, mul_one, card_Icc_int]
lemma card_faceV (n : ℕ) (c : ℤ) :
    (({(c)} : Finset ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
  rw [Finset.card_product, Finset.card_singleton, one_mul, card_Icc_int]
def truncPhase (α β : ℝ) (n : ℕ) (x : Site) : ℂ :=
  if x ∈ boxF n then phase α β x else 0
lemma truncPhase_apply_of_mem {α β : ℝ} {n : ℕ} {x : Site} (hx : x ∈ boxF n) :
    truncPhase α β n x = phase α β x := by
  simp [truncPhase, hx]
lemma truncPhase_apply_of_not_mem {α β : ℝ} {n : ℕ} {x : Site} (hx : x ∉ boxF n) :
    truncPhase α β n x = 0 := by
  simp [truncPhase, hx]
lemma norm_truncPhase_le (α β : ℝ) (n : ℕ) (x : Site) : ‖truncPhase α β n x‖ ≤ 1 := by
  by_cases hx : x ∈ boxF n
  · rw [truncPhase_apply_of_mem hx, norm_phase]
  · rw [truncPhase_apply_of_not_mem hx, norm_zero]; norm_num
lemma memℓp_truncPhase (α β : ℝ) (n : ℕ) : Memℓp (truncPhase α β n) 2 := by
  refine memℓp_gen ?_
  refine summable_of_ne_finset_zero (s := boxF n)
    (f := fun x : Site => ‖truncPhase α β n x‖ ^ (2 : ℝ≥0∞).toReal) ?_
  intro x hx
  rw [truncPhase_apply_of_not_mem hx, norm_zero, Real.zero_rpow (by norm_num)]
def truncVec (α β : ℝ) (n : ℕ) : Hilbert :=
  ⟨truncPhase α β n, memℓp_truncPhase α β n⟩
lemma truncVec_apply (α β : ℝ) (n : ℕ) (x : Site) :
    (truncVec α β n : Site → ℂ) x = truncPhase α β n x := rfl
lemma norm_sq_eq_sum_of_support_subset {f : Hilbert} {S : Finset Site}
    (h : ∀ x, x ∉ S → (f : Site → ℂ) x = 0) :
    ‖f‖ ^ 2 = ∑ x ∈ S, ‖(f : Site → ℂ) x‖ ^ 2 := by
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) hp f
  rw [ENNReal.toReal_ofNat] at h1
  have h2 : (∑' i : Site, ‖(f : Site → ℂ) i‖ ^ (2 : ℝ))
      = ∑ x ∈ S, ‖(f : Site → ℂ) x‖ ^ (2 : ℝ) := by
    refine tsum_eq_sum ?_
    intro i hi
    rw [h i hi, norm_zero, Real.zero_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  have h3 : (∑ x ∈ S, ‖(f : Site → ℂ) x‖ ^ (2 : ℝ))
      = ∑ x ∈ S, ‖(f : Site → ℂ) x‖ ^ 2 :=
    Finset.sum_congr rfl (fun x _ => Real.rpow_two _)
  rw [h2, h3, Real.rpow_two] at h1
  exact h1
lemma norm_truncVec (α β : ℝ) (n : ℕ) : ‖truncVec α β n‖ = (2 * n + 1 : ℝ) := by
  have hsq : ‖truncVec α β n‖ ^ 2 = ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_sq_eq_sum_of_support_subset (f := truncVec α β n) (S := boxF n) (by
      intro x hx
      rw [truncVec_apply, truncPhase_apply_of_not_mem hx])]
    have hstep : (∑ x ∈ boxF n, ‖(truncVec α β n : Site → ℂ) x‖ ^ 2)
        = ∑ _x ∈ boxF n, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [truncVec_apply, truncPhase_apply_of_mem hx, norm_phase]
      norm_num
    rw [hstep, Finset.sum_const, nsmul_eq_mul, mul_one, card_boxF]
    push_cast
    ring
  have hnn : (0 : ℝ) ≤ ‖truncVec α β n‖ := norm_nonneg _
  have hpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · rw [h]; push_cast; ring
  · rw [h] at hnn; linarith
lemma norm_truncVec_pos (α β : ℝ) (n : ℕ) : ‖truncVec α β n‖ ≠ 0 := by
  rw [norm_truncVec]; positivity
lemma truncVec_ne_zero (α β : ℝ) (n : ℕ) : truncVec α β n ≠ 0 := by
  intro h
  have := norm_truncVec_pos α β n
  rw [h, norm_zero] at this
  exact this rfl
lemma cps_cos_arccos_param {c lam : ℝ} (h1 : c - 4 ≤ lam) (h2 : lam ≤ c + 4) :
    2 * Real.cos (Real.arccos ((lam - c) / 4)) + 2 * Real.cos (Real.arccos ((lam - c) / 4))
      = lam - c := by
  have hlo : -1 ≤ (lam - c) / 4 := by linarith
  have hhi : (lam - c) / 4 ≤ 1 := by linarith
  rw [Real.cos_arccos hlo hhi]
  ring
lemma cps_boxF_mono {a b : ℕ} (hab : a ≤ b) : boxF a ⊆ boxF b := by
  intro x hx
  rw [mem_boxF] at hx ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hab' : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
lemma cps_neighbor_mem_boxF {m : ℕ} (hm : 1 ≤ m) {x : Site} (hx : x ∈ boxF (m - 1)) :
    (x.1 + 1, x.2) ∈ boxF m ∧ (x.1 - 1, x.2) ∈ boxF m ∧
      (x.1, x.2 + 1) ∈ boxF m ∧ (x.1, x.2 - 1) ∈ boxF m := by
  have hmc : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
    have h : ((m - 1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) = ((m : ℕ) : ℤ) := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hm]
    push_cast at h
    linarith
  rw [mem_boxF] at hx
  obtain ⟨h1, h2, h3, h4⟩ := hx
  rw [hmc] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_boxF] <;> omega
def cps_unitCoeff (m : ℕ) : ℝ := 1 / (2 * (m : ℝ) + 1)
lemma cps_unitCoeff_pos (m : ℕ) : 0 < cps_unitCoeff m := by
  rw [cps_unitCoeff]; positivity
lemma cps_norm_unitCoeff (m : ℕ) : ‖(cps_unitCoeff m : ℂ)‖ = cps_unitCoeff m := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cps_unitCoeff_pos m)]
def cps_unitVec (α β : ℝ) (m : ℕ) : Hilbert := ((cps_unitCoeff m : ℝ) : ℂ) • truncVec α β m
lemma cps_unitVec_apply (α β : ℝ) (m : ℕ) (x : Site) :
    ((cps_unitVec α β m : Hilbert) : Site → ℂ) x = (cps_unitCoeff m : ℂ) * truncPhase α β m x := by
  rw [cps_unitVec, lp.coeFn_smul]
  rfl
lemma cps_norm_unitVec (α β : ℝ) (m : ℕ) : ‖cps_unitVec α β m‖ = 1 := by
  rw [cps_unitVec, norm_smul, cps_norm_unitCoeff, norm_truncVec, cps_unitCoeff]
  have h : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
lemma cps_norm_unitVec_apply_le (α β : ℝ) (m : ℕ) (x : Site) :
    ‖((cps_unitVec α β m : Hilbert) : Site → ℂ) x‖ ≤ cps_unitCoeff m := by
  rw [cps_unitVec_apply, norm_mul, cps_norm_unitCoeff]
  calc cps_unitCoeff m * ‖truncPhase α β m x‖ ≤ cps_unitCoeff m * 1 :=
        mul_le_mul_of_nonneg_left (norm_truncPhase_le α β m x) (le_of_lt (cps_unitCoeff_pos m))
    _ = cps_unitCoeff m := mul_one _
lemma cps_unitVec_apply_eq_zero (α β : ℝ) {m : ℕ} {x : Site} (hx : x ∉ boxF m) :
    ((cps_unitVec α β m : Hilbert) : Site → ℂ) x = 0 := by
  rw [cps_unitVec_apply, truncPhase_apply_of_not_mem hx, mul_zero]
lemma cps_sub_smul_one_apply {v : Configuration} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator v H) (lam : ℝ) (u : Hilbert) (x : Site) :
    (((H - (lam : ℂ) • 1) u : Hilbert) : Site → ℂ) x =
      (u (x.1 + 1, x.2) + u (x.1 - 1, x.2) + u (x.1, x.2 + 1) + u (x.1, x.2 - 1))
        + ((v x : ℂ) - (lam : ℂ)) * u x := by
  have h1 : ((H - (lam : ℂ) • 1) u : Hilbert) =
      H u - (((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u) := by
    rw [ContinuousLinearMap.sub_apply]
  rw [h1]
  have h2 : ((((H u - (((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u)) : Hilbert)) : Site → ℂ) x
      = ((H u : Hilbert) : Site → ℂ) x -
        (((((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u : Hilbert)) : Site → ℂ) x := by
    rw [lp.coeFn_sub]
    rfl
  rw [h2]
  have h3 : ((((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u : Hilbert)) = (lam : ℂ) • u := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [h3]
  have h4 : ((((lam : ℂ) • u : Hilbert)) : Site → ℂ) x = (lam : ℂ) * ((u : Hilbert) : Site → ℂ) x := by
    rw [lp.coeFn_smul]
    rfl
  rw [h4, hop u x]
  ring
lemma cps_interior_zero {c lam α : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator (fun _ : Site => c) H)
    (hα : 2 * Real.cos α + 2 * Real.cos α = lam - c)
    {m : ℕ} (hm : 1 ≤ m) {x : Site} (hx : x ∈ boxF (m - 1)) :
    (((H - (lam : ℂ) • 1) (cps_unitVec α α m) : Hilbert) : Site → ℂ) x = 0 := by
  have hxbox : x ∈ boxF m := cps_boxF_mono (by omega : m - 1 ≤ m) hx
  obtain ⟨ha, hb, hc, hd⟩ := cps_neighbor_mem_boxF hm hx
  rw [cps_sub_smul_one_apply hop]
  rw [cps_unitVec_apply, cps_unitVec_apply, cps_unitVec_apply, cps_unitVec_apply, cps_unitVec_apply]
  rw [truncPhase_apply_of_mem ha, truncPhase_apply_of_mem hb, truncPhase_apply_of_mem hc,
      truncPhase_apply_of_mem hd, truncPhase_apply_of_mem hxbox]
  have hP : phase α α (x.1 + 1, x.2) + phase α α (x.1 - 1, x.2) + phase α α (x.1, x.2 + 1) +
      phase α α (x.1, x.2 - 1) = ((lam : ℂ) - (c : ℂ)) * phase α α x := by
    rw [phase_neighbors]
    rw [show ((2 * Real.cos α + 2 * Real.cos α : ℝ) : ℂ) = ((lam - c : ℝ) : ℂ) by rw [hα]]
    push_cast
    ring
  rw [show (cps_unitCoeff m : ℂ) * phase α α (x.1 + 1, x.2) + (cps_unitCoeff m : ℂ) * phase α α (x.1 - 1, x.2) +
        (cps_unitCoeff m : ℂ) * phase α α (x.1, x.2 + 1) + (cps_unitCoeff m : ℂ) * phase α α (x.1, x.2 - 1)
      = (cps_unitCoeff m : ℂ) * (phase α α (x.1 + 1, x.2) + phase α α (x.1 - 1, x.2) +
        phase α α (x.1, x.2 + 1) + phase α α (x.1, x.2 - 1)) from by ring]
  rw [hP]
  ring
def cps_boxShell (m : ℕ) : Finset Site := boxF (m + 1) \ boxF (m - 1)
lemma cps_card_boxShell {m : ℕ} (hm : 1 ≤ m) : (cps_boxShell m).card = 16 * m + 8 := by
  have hsub : boxF (m - 1) ⊆ boxF (m + 1) := cps_boxF_mono (by omega)
  have hinter : boxF (m - 1) ∩ boxF (m + 1) = boxF (m - 1) := Finset.inter_eq_left.2 hsub
  rw [cps_boxShell, Finset.card_sdiff, hinter, card_boxF, card_boxF]
  have hexp : (2 * (m + 1) + 1) ^ 2 - (2 * (m - 1) + 1) ^ 2 = 16 * m + 8 := by
    have h2 : 2 * (m - 1) + 1 = 2 * m - 1 := by omega
    rw [h2]
    have h1 : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
    rw [h1]
    have hle : (2 * m - 1) ^ 2 ≤ (2 * m + 3) ^ 2 := by
      apply Nat.pow_le_pow_left; omega
    rw [Nat.sub_eq_iff_eq_add hle]
    have key : (((2 * m + 3) ^ 2 : ℕ) : ℤ) =
        ((16 * m + 8 : ℕ) : ℤ) + (((2 * m - 1) ^ 2 : ℕ) : ℤ) := by
      have h3 : ((2 * m - 1 : ℕ) : ℤ) = 2 * (m : ℤ) - 1 := by
        have : 1 ≤ 2 * m := by omega
        rw [Nat.cast_sub this]; push_cast; ring
      push_cast [h3]
      ring
    exact_mod_cast key
  rw [hexp]
lemma cps_mem_boxShell {m : ℕ} {x : Site} :
    x ∈ cps_boxShell m ↔ x ∈ boxF (m + 1) ∧ x ∉ boxF (m - 1) := by
  rw [cps_boxShell, Finset.mem_sdiff]
lemma cps_not_mem_boxF_of_neighbor {m : ℕ} {x : Site} (hx : x ∉ boxF (m + 1)) :
    (x.1 + 1, x.2) ∉ boxF m ∧ (x.1 - 1, x.2) ∉ boxF m ∧
      (x.1, x.2 + 1) ∉ boxF m ∧ (x.1, x.2 - 1) ∉ boxF m := by
  have hmc : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
  rw [mem_boxF] at hx
  push_neg at hx
  have hmc' : ((m : ℕ) : ℤ) = (m : ℤ) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mem_boxF] <;> push_neg <;> omega
lemma cps_leakage_apply_eq_zero {c lam α : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator (fun _ : Site => c) H) (hα : 2 * Real.cos α + 2 * Real.cos α = lam - c)
    {m : ℕ} (hm : 1 ≤ m) {x : Site} (hx : x ∉ cps_boxShell m) :
    (((H - (lam : ℂ) • 1) (cps_unitVec α α m) : Hilbert) : Site → ℂ) x = 0 := by
  by_cases hout : x ∈ boxF (m + 1)
  ·                                                    
    have hin : x ∈ boxF (m - 1) := by
      by_contra hc
      exact hx (cps_mem_boxShell.2 ⟨hout, hc⟩)
    exact cps_interior_zero hop hα hm hin
  ·                                                                             
    obtain ⟨ha, hb, hc, hd⟩ := cps_not_mem_boxF_of_neighbor (m := m) hout
    rw [cps_sub_smul_one_apply hop]
    rw [cps_unitVec_apply_eq_zero α α ha, cps_unitVec_apply_eq_zero α α hb,
        cps_unitVec_apply_eq_zero α α hc, cps_unitVec_apply_eq_zero α α hd]
    by_cases hxmem : x ∈ boxF m
    · have : x ∈ boxF (m + 1) := cps_boxF_mono (by omega) hxmem
      exact absurd this hout
    · rw [cps_unitVec_apply_eq_zero α α hxmem]
      ring
lemma cps_apply_sub_smul_one_norm_le {v : Configuration} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator v H) (lam : ℝ) (u : Hilbert) (K : ℝ)
    (hu : ∀ x : Site, ‖((u : Hilbert) : Site → ℂ) x‖ ≤ K) (x : Site) :
    ‖(((H - (lam : ℂ) • 1) u : Hilbert) : Site → ℂ) x‖ ≤ 4 * K + ‖v x‖ * K + ‖lam‖ * K := by
  rw [cps_sub_smul_one_apply hop]
  have hn : ‖((v x : ℂ) - (lam : ℂ)) * ((u : Hilbert) : Site → ℂ) x‖ =
      ‖((v x : ℂ) - (lam : ℂ))‖ * ‖((u : Hilbert) : Site → ℂ) x‖ := norm_mul _ _
                                 
  have h1 : ‖u (x.1 + 1, x.2)‖ ≤ K := hu _
  have h2 : ‖u (x.1 - 1, x.2)‖ ≤ K := hu _
  have h3 : ‖u (x.1, x.2 + 1)‖ ≤ K := hu _
  have h4 : ‖u (x.1, x.2 - 1)‖ ≤ K := hu _
  have hvx : ‖((v x : ℂ) - (lam : ℂ))‖ ≤ ‖v x‖ + ‖lam‖ := by
    have hcast : ((v x : ℂ) - (lam : ℂ)) = (((v x - lam : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_sub_le_iff.2 ⟨by linarith [le_abs_self (v x), neg_abs_le (lam)], by
      linarith [neg_abs_le (v x), le_abs_self (lam)]⟩
  have hvlx : (0:ℝ) ≤ ‖v x‖ + ‖lam‖ := by positivity
  have h5 : ‖((v x : ℂ) - (lam : ℂ)) * ((u : Hilbert) : Site → ℂ) x‖ ≤ (‖v x‖ + ‖lam‖) * K := by
    rw [hn]
    exact mul_le_mul hvx (hu x) (norm_nonneg _) hvlx
  calc ‖u (x.1 + 1, x.2) + u (x.1 - 1, x.2) + u (x.1, x.2 + 1) + u (x.1, x.2 - 1) +
        ((v x : ℂ) - (lam : ℂ)) * ((u : Hilbert) : Site → ℂ) x‖
      ≤ ‖u (x.1 + 1, x.2) + u (x.1 - 1, x.2) + u (x.1, x.2 + 1) + u (x.1, x.2 - 1)‖ +
        ‖((v x : ℂ) - (lam : ℂ)) * ((u : Hilbert) : Site → ℂ) x‖ := norm_add_le _ _
    _ ≤ (‖u (x.1 + 1, x.2)‖ + ‖u (x.1 - 1, x.2)‖ + ‖u (x.1, x.2 + 1)‖ + ‖u (x.1, x.2 - 1)‖) +
        (‖v x‖ + ‖lam‖) * K := by
        gcongr
        exact norm_add₄_le
    _ ≤ (K + K + K + K) + (‖v x‖ + ‖lam‖) * K := by gcongr
    _ = 4 * K + ‖v x‖ * K + ‖lam‖ * K := by ring
lemma cps_leakage_norm_sq_le {c lam α : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator (fun _ : Site => c) H)
    (hα : 2 * Real.cos α + 2 * Real.cos α = lam - c)
    {m : ℕ} (hm : 1 ≤ m) :
    ‖(H - (lam : ℂ) • 1) (cps_unitVec α α m)‖ ^ 2 ≤
      (16 * (m : ℝ) + 8) * ((4 + |c| + |lam|) / (2 * (m : ℝ) + 1)) ^ 2 := by
  have hKpos : 0 < cps_unitCoeff m := cps_unitCoeff_pos m
  have hDnonneg : (0:ℝ) ≤ 4 + |c| + |lam| := by positivity
  have hper : ∀ x ∈ cps_boxShell m,
      ‖(((H - (lam : ℂ) • 1) (cps_unitVec α α m) : Hilbert) : Site → ℂ) x‖ ^ 2 ≤
        ((4 + |c| + |lam|) * cps_unitCoeff m) ^ 2 := by
    intro x _
    have hb := cps_apply_sub_smul_one_norm_le hop lam (cps_unitVec α α m) (cps_unitCoeff m)
      (fun y => cps_norm_unitVec_apply_le α α m y) x
    have heq : 4 * cps_unitCoeff m + ‖c‖ * cps_unitCoeff m + ‖lam‖ * cps_unitCoeff m
        = (4 + |c| + |lam|) * cps_unitCoeff m := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      ring
    have hb' : ‖(((H - (lam : ℂ) • 1) (cps_unitVec α α m) : Hilbert) : Site → ℂ) x‖ ≤
        (4 + |c| + |lam|) * cps_unitCoeff m := by
      rw [← heq]; exact hb
    have h2 : (0:ℝ) ≤ (4 + |c| + |lam|) * cps_unitCoeff m := by positivity
    exact pow_le_pow_left₀ (norm_nonneg _) hb' 2
  rw [norm_sq_eq_sum_of_support_subset (f := (H - (lam : ℂ) • 1) (cps_unitVec α α m))
      (S := cps_boxShell m) (fun x hx => cps_leakage_apply_eq_zero hop hα hm hx)]
  calc ∑ x ∈ cps_boxShell m, ‖(((H - (lam : ℂ) • 1) (cps_unitVec α α m) : Hilbert) : Site → ℂ) x‖ ^ 2
      ≤ ∑ _x ∈ cps_boxShell m, ((4 + |c| + |lam|) * cps_unitCoeff m) ^ 2 := Finset.sum_le_sum hper
    _ = (cps_boxShell m).card • ((4 + |c| + |lam|) * cps_unitCoeff m) ^ 2 := Finset.sum_const _
    _ = (16 * (m : ℝ) + 8) * ((4 + |c| + |lam|) / (2 * (m : ℝ) + 1)) ^ 2 := by
        rw [cps_card_boxShell hm, nsmul_eq_mul, cps_unitCoeff]
        push_cast
        ring
lemma cps_mem_spectrum_of_approx (T : Hilbert →L[ℂ] Hilbert) (z : ℂ)
    (h : ∀ eps : ℝ, 0 < eps → ∃ u : Hilbert, ‖u‖ = 1 ∧
      ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ < eps) :
    z ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨R, hR⟩ := hunit.exists_left_inv
  have hRnn : (0:ℝ) ≤ ‖R‖ := norm_nonneg _
  have heps : (0:ℝ) < 1 / (2 * (‖R‖ + 1)) := by positivity
  obtain ⟨u, hu1, hu2⟩ := h (1 / (2 * (‖R‖ + 1))) heps
  have happ : (R * (algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T)) u = u := by
    rw [hR, ContinuousLinearMap.one_apply]
  have h1 : (1:ℝ) ≤ ‖R‖ * ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ := by
    have hbase : ‖u‖ ≤ ‖R‖ * ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ := by
      calc ‖u‖ = ‖(R * (algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T)) u‖ := by rw [happ]
        _ = ‖R ((algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u)‖ := rfl
        _ ≤ ‖R‖ * ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ := ContinuousLinearMap.le_opNorm _ _
    rw [hu1] at hbase; exact hbase
  have hbound : ‖R‖ * ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ < 1 := by
    have hstep : ‖R‖ * ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - T) u‖ ≤
        ‖R‖ * (1 / (2 * (‖R‖ + 1))) := by
      rcases eq_or_lt_of_le hRnn with h0 | hpos
      · rw [← h0]; simp
      · exact le_of_lt (mul_lt_mul_of_pos_left hu2 hpos)
    have hfin : ‖R‖ * (1 / (2 * (‖R‖ + 1))) < 1 := by
      rw [mul_one_div]
      rw [div_lt_one (by positivity : (0:ℝ) < 2 * (‖R‖ + 1))]
      linarith
    linarith
  linarith
lemma cps_shell_ratio_le {m : ℕ} (hm : 1 ≤ m) :
    (16 * (m : ℝ) + 8) / (2 * (m : ℝ) + 1) ^ 2 ≤ 6 / (m : ℝ) := by
  have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hden : (0:ℝ) < (2 * (m : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ hmpos]
  nlinarith [hmpos, sq_nonneg ((m:ℝ) - 1)]
theorem ae_blocks_simultaneous {h : ℝ} (hh : 0 < h)
    (Hblk : ∀ c ∈ Set.Icc (-h) h, ∀ ε > 0, ∀ N : ℕ, ∀ᵐ v ∂disorderLaw h,
      ∃ (a : Site) (n : ℕ), N ≤ n ∧ ∀ x : Site,
        (x.1 - a.1).natAbs ≤ n → (x.2 - a.2).natAbs ≤ n → |v x - c| < ε) :
    ∀ᵐ v ∂disorderLaw h, ∀ c ∈ Set.Icc (-h) h, ∀ ε > 0, ∀ N : ℕ,
      ∃ (a : Site) (n : ℕ), N ≤ n ∧ ∀ x : Site,
        (x.1 - a.1).natAbs ≤ n → (x.2 - a.2).natAbs ≤ n → |v x - c| < ε := by
  have hall : ∀ᵐ v ∂disorderLaw h, ∀ p : ℚ × ℚ × ℕ,
      ((p.1 : ℝ) ∈ Set.Icc (-h) h) → 0 < ((p.2.1 : ℚ) : ℝ) →
      ∃ (a : Site) (n : ℕ), p.2.2 ≤ n ∧ ∀ x : Site,
        (x.1 - a.1).natAbs ≤ n → (x.2 - a.2).natAbs ≤ n →
          |v x - (p.1 : ℝ)| < ((p.2.1 : ℚ) : ℝ) := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    by_cases hc : ((p.1 : ℝ) ∈ Set.Icc (-h) h)
    · by_cases he : 0 < ((p.2.1 : ℚ) : ℝ)
      · exact (Hblk _ hc _ he _).mono (fun v hv _ _ => hv)
      · exact Filter.Eventually.of_forall (fun v _ he' => absurd he' he)
    · exact Filter.Eventually.of_forall (fun v hc' => absurd hc' hc)
  filter_upwards [hall] with v hv c hc ε he N
  have hc1 : -h ≤ c := hc.1
  have hc2 : c ≤ h := hc.2
  have hpos : (0:ℝ) < h := hh
  have he2 : (0:ℝ) < ε/2 := by linarith
  have hlt : max (-h) (c - ε/2) < min h (c + ε/2) := by
    refine max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨by linarith, by linarith⟩,
      lt_min_iff.mpr ⟨by linarith, by linarith⟩⟩
  obtain ⟨cq, hq1, hq2⟩ := exists_rat_btwn hlt
  obtain ⟨eq, he1, he2'⟩ := exists_rat_btwn he2
  have hcq_mem : ((cq : ℝ) ∈ Set.Icc (-h) h) := by
    rw [Set.mem_Icc]
    exact ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hq1),
      le_of_lt (lt_of_lt_of_le hq2 (min_le_left _ _))⟩
  obtain ⟨a, n, hn, hblk⟩ := hv (cq, eq, N) hcq_mem he1
  refine ⟨a, n, hn, fun x h1 h2 => ?_⟩
  have hb := hblk x h1 h2
  have hdist : |(cq : ℝ) - c| < ε/2 := by
    rw [abs_lt]
    exact ⟨by linarith [lt_of_le_of_lt (le_max_right _ _) hq1],
           by linarith [lt_of_lt_of_le hq2 (min_le_right _ _)]⟩
  calc |v x - c| = |(v x - (cq:ℝ)) + ((cq:ℝ) - c)| := by ring_nf
    _ ≤ |v x - (cq:ℝ)| + |(cq:ℝ) - c| := abs_add_le _ _
    _ < ε/2 + ε/2 := by linarith
    _ = ε := by ring
theorem anderson_from_components {h : ℝ} (hh : 0 < h)
    (hb : ∀ᵐ v ∂disorderLaw h, ∀ x : Site, |v x| ≤ h)
    (hup : ∀ (v : Configuration) (H : Hilbert →L[ℂ] Hilbert), (∀ x : Site, |v x| ≤ h) →
      IsAndersonOperator v H → IsSelfAdjoint H → spectrum ℂ H ⊆ spectralInterval h)
    (hlow : ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectralInterval h ⊆ spectrum ℂ H) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  filter_upwards [hb, hlow] with v hbv hlowv
  obtain ⟨H, hop, hsa, hsub⟩ := hlowv
  exact ⟨H, hop, hsa, Set.Subset.antisymm (hup v H hbv hop hsa) hsub⟩
lemma shiftLp_comp (a b : Site) (u : Hilbert) :
    shiftLp a (shiftLp b u) = shiftLp (a + b) u := by
  ext x
  simp only [shiftLp_coe, add_assoc]
lemma shiftLp_zero (u : Hilbert) : shiftLp 0 u = u := by
  ext x
  simp only [shiftLp_coe, add_zero]
lemma shiftLp_neg_comp (a : Site) (u : Hilbert) :
    shiftLp (-a) (shiftLp a u) = u := by
  rw [shiftLp_comp]
  simp only [neg_add_cancel, shiftLp_zero]
lemma shiftCLM_mul (a b : Site) : shiftCLM a * shiftCLM b = shiftCLM (a + b) := by
  ext u
  rw [ContinuousLinearMap.mul_apply, shiftCLM_apply, shiftCLM_apply, shiftCLM_apply, shiftLp_comp]
lemma shiftCLM_neg_mul (a : Site) : shiftCLM (-a) * shiftCLM a = 1 := by
  rw [shiftCLM_mul]
  rw [show -a + a = 0 by abel]
  ext u
  rw [shiftCLM_apply, shiftLp_zero]
  rfl
lemma shiftCLM_mul_neg (a : Site) : shiftCLM a * shiftCLM (-a) = 1 := by
  rw [shiftCLM_mul]
  rw [show a + -a = 0 by abel]
  ext u
  rw [shiftCLM_apply, shiftLp_zero]
  rfl
lemma shiftCLM_apply_apply (a : Site) (T : Hilbert →L[ℂ] Hilbert) (u : Hilbert) (x : Site) :
    ((shiftCLM a * T * shiftCLM (-a)) u : Hilbert) x = (T (shiftCLM (-a) u) : Hilbert) (x + a) := by
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [shiftCLM_apply, shiftLp_coe]
lemma isAndersonOperator_shift (a : Site) {v : Configuration} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator v H) :
    IsAndersonOperator (fun x : Site => v (x + a)) (shiftCLM a * H * shiftCLM (-a)) := by
  intro u x
  rw [shiftCLM_apply_apply]
  have hcoe : ((shiftCLM (-a)) u : Hilbert) = shiftLp (-a) u := shiftCLM_apply (-a) u
  rw [hcoe]
  change (H (shiftLp (-a) u) : Site → ℂ) (x + a) =
    (u : Site → ℂ) (x.1 + 1, x.2) + (u : Site → ℂ) (x.1 - 1, x.2) +
      (u : Site → ℂ) (x.1, x.2 + 1) + (u : Site → ℂ) (x.1, x.2 - 1) +
      (v (x + a) : ℂ) * (u : Site → ℂ) x
  rw [hop (shiftLp (-a) u) (x + a)]
  simp only [shiftLp_coe]
  have hx1 : ((x + a).1 + 1, (x + a).2) + -a = (x.1 + 1, x.2) := by ext <;> simp <;> ring
  have hx2 : ((x + a).1 - 1, (x + a).2) + -a = (x.1 - 1, x.2) := by ext <;> simp <;> ring
  have hx3 : ((x + a).1, (x + a).2 + 1) + -a = (x.1, x.2 + 1) := by ext <;> simp <;> ring
  have hx4 : ((x + a).1, (x + a).2 - 1) + -a = (x.1, x.2 - 1) := by ext <;> simp <;> ring
  rw [hx1, hx2, hx3, hx4]
  have hun : (x + a + -a) = x := by abel
  rw [hun]
lemma cps_constant_approx {c lam : ℝ} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator (fun _ : Site => c) H)
    (h1 : c - 4 ≤ lam) (h2 : lam ≤ c + 4) :
    ∀ eps > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ m : ℕ, N ≤ m →
      ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
          (cps_unitVec (Real.arccos ((lam - c) / 4))
             (Real.arccos ((lam - c) / 4)) m)‖ < eps := by
  intro eps heps
  let α : ℝ := Real.arccos ((lam - c) / 4)
  have hα : 2 * Real.cos α + 2 * Real.cos α = lam - c := by
    dsimp only [α]
    exact cps_cos_arccos_param h1 h2
  have hA0 : (0:ℝ) ≤ 4 + |c| + |lam| := by positivity
  have heps2 : (0:ℝ) < (eps / 4) ^ 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (6 * (4 + |c| + |lam|) ^ 2 / (eps / 4) ^ 2))
  have hN1R : (1:ℝ) ≤ (N:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left (1:ℝ) _) hN)
  have hN1 : 1 ≤ N := by exact_mod_cast hN1R
  refine ⟨N, hN1, ?_⟩
  · intro m hm
    have hmN : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm1 : 1 ≤ m := le_trans hN1 hm
    have hmpos : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hleak := cps_leakage_norm_sq_le (c := c) (lam := lam) (α := α) hop hα hm1
    have hratio := cps_shell_ratio_le (m := m) hm1
    have hprod : (16 * (m : ℝ) + 8) * ((4 + |c| + |lam|) / (2 * (m : ℝ) + 1)) ^ 2
        = (4 + |c| + |lam|) ^ 2 * ((16 * (m : ℝ) + 8) / (2 * (m : ℝ) + 1) ^ 2) := by
      have hden : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have hsq : ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α m)‖ ^ 2
        ≤ 6 * (4 + |c| + |lam|) ^ 2 / (m : ℝ) := by
      calc ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α m)‖ ^ 2
          ≤ (16 * (m : ℝ) + 8) * ((4 + |c| + |lam|) / (2 * (m : ℝ) + 1)) ^ 2 := hleak
        _ = (4 + |c| + |lam|) ^ 2 * ((16 * (m : ℝ) + 8) / (2 * (m : ℝ) + 1) ^ 2) := hprod
        _ ≤ (4 + |c| + |lam|) ^ 2 * (6 / (m : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
        _ = 6 * (4 + |c| + |lam|) ^ 2 / (m : ℝ) := by ring
    have hbig : 6 * (4 + |c| + |lam|) ^ 2 / (eps / 4) ^ 2 < (m : ℝ) := by
      have hlt : 6 * (4 + |c| + |lam|) ^ 2 / (eps / 4) ^ 2 < (N : ℝ) :=
        lt_of_le_of_lt (le_max_right (1:ℝ) _) hN
      linarith
    have hsmall : 6 * (4 + |c| + |lam|) ^ 2 / (m : ℝ) < (eps / 4) ^ 2 := by
      rw [div_lt_iff₀ hmpos]
      have := (div_lt_iff₀ heps2).mp hbig
      nlinarith
    have hsqlt :
        ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α m)‖ ^ 2
          < (eps / 4) ^ 2 := lt_of_le_of_lt hsq hsmall
    have hn0 : (0:ℝ) ≤ ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α m)‖ :=
      norm_nonneg _
    have hquarter : (0:ℝ) ≤ eps / 4 := by positivity
    have habs := (sq_lt_sq).mp hsqlt
    rw [abs_of_nonneg hn0, abs_of_nonneg hquarter] at habs
    linarith
lemma andersonOperator_sub_apply {c : ℝ} {v : Configuration}
    {H Hc : Hilbert →L[ℂ] Hilbert} (hop : IsAndersonOperator v H)
    (hopc : IsAndersonOperator (fun _ : Site => c) Hc) (u : Hilbert) (x : Site) :
    (((H - Hc) u : Hilbert) : Site → ℂ) x =
      (((v x - c : ℝ) : ℂ) * ((u : Hilbert) : Site → ℂ) x) := by
  rw [ContinuousLinearMap.sub_apply]
  rw [lp.coeFn_sub]
  rw [Pi.sub_apply]
  rw [hop u x, hopc u x]
  push_cast
  ring
lemma nearConstant_sub_norm_le {c ε : ℝ} {v : Configuration}
    {H Hc : Hilbert →L[ℂ] Hilbert} {n : ℕ} {u : Hilbert}
    (hop : IsAndersonOperator v H)
    (hopc : IsAndersonOperator (fun _ : Site => c) Hc)
    (hε : 0 < ε)
    (hblk : ∀ x : Site, x ∈ boxF n → |v x - c| < ε / 2)
    (hu : ∀ x : Site, x ∉ boxF n → ((u : Hilbert) : Site → ℂ) x = 0) :
    ‖(H - Hc) u‖ ≤ (ε / 2) * ‖u‖ := by
  have hhalf : (0:ℝ) < ε / 2 := by linarith
  have hpoint : ∀ x : Site,
      ‖(((H - Hc) u : Hilbert) : Site → ℂ) x‖
        ≤ ‖(((((ε / 2 : ℝ) : ℂ) • u : Hilbert)) : Site → ℂ) x‖ := by
    intro x
    by_cases hx : x ∈ boxF n
    · have hleft : ‖(((H - Hc) u : Hilbert) : Site → ℂ) x‖ ≤ (ε / 2) * ‖((u : Hilbert) : Site → ℂ) x‖ := by
        rw [andersonOperator_sub_apply hop hopc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hblk x hx)) (norm_nonneg _)
      have hright : ‖(((((ε / 2 : ℝ) : ℂ) • u : Hilbert)) : Site → ℂ) x‖
          = (ε / 2) * ‖((u : Hilbert) : Site → ℂ) x‖ := by
        rw [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (le_of_lt hhalf)]
      rw [hright]
      exact hleft
    · have hux : ((u : Hilbert) : Site → ℂ) x = 0 := hu x hx
      have hleft : ‖(((H - Hc) u : Hilbert) : Site → ℂ) x‖ = 0 := by
        rw [andersonOperator_sub_apply hop hopc, hux, mul_zero, norm_zero]
      have hright : ‖(((((ε / 2 : ℝ) : ℂ) • u : Hilbert)) : Site → ℂ) x‖ = 0 := by
        rw [lp.coeFn_smul, Pi.smul_apply, hux, smul_zero, norm_zero]
      rw [hleft, hright]
  have hmono := lp.norm_mono (p := 2) (E := fun _ : Site => ℂ) (F := fun _ : Site => ℂ)
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (x := (H - Hc) u)
    (y := (((ε / 2 : ℝ) : ℂ) • u)) hpoint
  calc ‖(H - Hc) u‖ ≤ ‖(((ε / 2 : ℝ) : ℂ) • u)‖ := hmono
    _ = (ε / 2) * ‖u‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hhalf)]
lemma finite_box_approx_eigenvector_center0_uniform
    (c lam : ℝ) (hmem : lam ∈ Set.Icc (-4 + c) (4 + c)) :
    ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧
      ∀ (v : Configuration) (H : Hilbert →L[ℂ] Hilbert),
        IsAndersonOperator v H → ∀ n : ℕ, N ≤ n →
        (∀ x : Site, x ∈ boxF n → |v x - c| < ε / 2) →
        ∃ u : Hilbert, ‖u‖ = 1 ∧
          ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u‖ < ε := by
  intro ε hε
  obtain ⟨Hc, hopc, -, -⟩ := anderson_operator_exists_selfAdjoint (h := |c|)
    (fun _ : Site => c) (fun _ => le_rfl)
  let α : ℝ := Real.arccos ((lam - c) / 4)
  obtain ⟨N, hN1, hN⟩ := cps_constant_approx (c := c) (lam := lam) (H := Hc) hopc
    (by linarith [hmem.1]) (by linarith [hmem.2]) (ε / 2) (by linarith)
  refine ⟨N, hN1, ?_⟩
  intro v H hop n hn hblk
  have hcps : ‖(Hc - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α n)‖ < ε / 2 := by
    simpa only [α] using hN n hn
  have hpert : ‖(H - Hc) (cps_unitVec α α n)‖ ≤ (ε / 2) * ‖cps_unitVec α α n‖ :=
    nearConstant_sub_norm_le hop hopc hε hblk (fun x hx => cps_unitVec_apply_eq_zero α α hx)
  rw [cps_norm_unitVec α α n, mul_one] at hpert
  refine ⟨cps_unitVec α α n, cps_norm_unitVec α α n, ?_⟩
  have hdecomp : H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)
      = (H - Hc) + (Hc - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) := by abel
  rw [hdecomp]
  have hsum : ((H - Hc) + (Hc - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)))
        (cps_unitVec α α n)
      = (H - Hc) (cps_unitVec α α n) +
        (Hc - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α n) := by
    rw [add_apply]
  rw [hsum]
  have htri := norm_add_le ((H - Hc) (cps_unitVec α α n))
    ((Hc - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (cps_unitVec α α n))
  linarith
lemma finite_box_approx_eigenvector_center0
    {v : Configuration} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator v H) (c lam : ℝ)
    (hmem : lam ∈ Set.Icc (-4 + c) (4 + c)) :
    ∀ ε > 0, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (∀ x : Site, x ∈ boxF n → |v x - c| < ε / 2) →
      ∃ u : Hilbert, ‖u‖ = 1 ∧
        ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u‖ < ε := by
  intro ε hε
  obtain ⟨N, hN1, hN⟩ :=
    finite_box_approx_eigenvector_center0_uniform c lam hmem ε hε
  exact ⟨N, hN1, fun n hn hblk => hN v H hop n hn hblk⟩
lemma norm_shiftCLM_apply (a : Site) (u : Hilbert) : ‖shiftCLM a u‖ = ‖u‖ := by
  rw [shiftCLM_apply, norm_shiftLp]
lemma shiftCLM_conj_sub_smul_one_apply (a : Site) (H : Hilbert →L[ℂ] Hilbert)
    (lam : ℝ) (w : Hilbert) :
    (((shiftCLM a * H * shiftCLM (-a) -
        (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) w)) =
      shiftCLM a
        (((H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
          (shiftCLM (-a) w))) := by
  apply lp.ext
  funext x
  have hleft : (((shiftCLM a * H * shiftCLM (-a) -
      (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) w : Hilbert) : Site → ℂ) x
      = (((shiftCLM a * H * shiftCLM (-a)) w : Hilbert) : Site → ℂ) x -
        (((((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) w) : Hilbert) : Site → ℂ) x := by
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply]
  have hright : ((shiftCLM a
        (((H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
          (shiftCLM (-a) w))) : Hilbert) : Site → ℂ) x
      = (shiftLp a (((H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
          (shiftCLM (-a) w))) : Site → ℂ) x := by
    rw [shiftCLM_apply]
  rw [hleft, hright, shiftLp_coe, shiftCLM_apply_apply]
  have hone : ((((lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) w) : Hilbert)
      = (lam : ℂ) • w := by
    rw [smul_apply, one_apply_eq_self]
  rw [hone, lp.coeFn_smul, Pi.smul_apply]
  have hsub : (((H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
      (shiftCLM (-a) w)) : Hilbert)
      = H (shiftCLM (-a) w) - (lam : ℂ) • (shiftCLM (-a) w) := by
    rw [sub_apply, smul_apply, one_apply_eq_self]
  rw [hsub, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply]
  rw [shiftCLM_apply, shiftLp_coe]
  have hadd : x + a + -a = x := by abel
  rw [hadd]
lemma finite_box_approx_eigenvector
    {v : Configuration} {H : Hilbert →L[ℂ] Hilbert}
    (hop : IsAndersonOperator v H) :
    ∀ (c lam : ℝ), lam ∈ Set.Icc (-4 + c) (4 + c) → ∀ ε > 0,
      ∃ N : ℕ, ∀ (a : Site) (n : ℕ), N ≤ n →
        (∀ x : Site,
          (x.1 - a.1).natAbs ≤ n →
          (x.2 - a.2).natAbs ≤ n →
          |v x - c| < ε / 2) →
        ∃ u : Hilbert, ‖u‖ = 1 ∧
          ‖(H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u‖ < ε := by
  intro c lam hmem ε hε
  obtain ⟨N0, hN01, hN0rest⟩ :=
    finite_box_approx_eigenvector_center0_uniform c lam hmem ε hε
  refine ⟨N0, ?_⟩
  intro a n hn hblk
  let v' : Configuration := fun x : Site => v (x + a)
  let H' : Hilbert →L[ℂ] Hilbert := shiftCLM a * H * shiftCLM (-a)
  have hop' : IsAndersonOperator v' H' := isAndersonOperator_shift a hop
  have hblk' : ∀ x : Site, x ∈ boxF n → |v' x - c| < ε / 2 := by
    intro x hx
    rw [mem_boxF] at hx
    have hx1 : x.1.natAbs ≤ n := by
      rw [natAbs_le_iff n x.1]
      rw [Finset.mem_Icc]
      exact ⟨hx.1, hx.2.1⟩
    have hx2 : x.2.natAbs ≤ n := by
      rw [natAbs_le_iff n x.2]
      rw [Finset.mem_Icc]
      exact ⟨hx.2.2.1, hx.2.2.2⟩
    have h1 : ((x + a).1 - a.1).natAbs ≤ n := by
      simpa using hx1
    have h2 : ((x + a).2 - a.2).natAbs ≤ n := by
      simpa using hx2
    change |v (x + a) - c| < ε / 2
    exact hblk (x + a) h1 h2
  obtain ⟨w, hw1, hwerr⟩ := hN0rest v' H' hop' n hn hblk'
  refine ⟨shiftCLM (-a) w, ?_, ?_⟩
  · rw [norm_shiftCLM_apply, hw1]
  · have hconj := shiftCLM_conj_sub_smul_one_apply a H lam w
    rw [show ((shiftCLM a * H * shiftCLM (-a) -
        (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) w)
        = shiftCLM a ((H - (lam : ℂ) • (1 : Hilbert →L[ℂ] Hilbert))
            (shiftCLM (-a) w)) from hconj] at hwerr
    rw [norm_shiftCLM_apply] at hwerr
    exact hwerr
theorem spectrum_lower_of_blocks_pos {h : ℝ} (hh : 0 < h)
    (v : Configuration) (H : Hilbert →L[ℂ] Hilbert)
    (hop : IsAndersonOperator v H)
    (hblk : ∀ c ∈ Set.Icc (-h) h, ∀ ε > 0, ∀ N : ℕ,
      ∃ (a : Site) (n : ℕ), N ≤ n ∧
        ∀ x : Site,
          (x.1 - a.1).natAbs ≤ n →
          (x.2 - a.2).natAbs ≤ n →
          |v x - c| < ε) :
    spectralInterval h ⊆ spectrum ℂ H := by
  intro z hz
  obtain ⟨hzim, hzlo, hzhi⟩ := hz
  set c : ℝ := max (-h) (min h z.re) with hcdef
  have hc_mem : c ∈ Set.Icc (-h) h := by
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left h z.re)
  have hzmem : z.re ∈ Set.Icc (-4 + c) (4 + c) := by
    rw [Set.mem_Icc]
    constructor
    · by_cases hzh : z.re ≤ h
      · have hmin : min h z.re = z.re := min_eq_right hzh
        by_cases hzn : -h ≤ z.re
        · have hceq : c = z.re := by rw [hcdef, hmin, max_eq_right hzn]
          rw [hceq]
          linarith
        · have hzn' : z.re ≤ -h := le_of_lt (lt_of_not_ge hzn)
          have hceq : c = -h := by rw [hcdef, hmin, max_eq_left hzn']
          rw [hceq]
          linarith
      · have hzh' : h ≤ z.re := le_of_lt (lt_of_not_ge hzh)
        have hmin : min h z.re = h := min_eq_left hzh'
        have hceq : c = h := by
          rw [hcdef, hmin, max_eq_right (by linarith)]
        rw [hceq]
        linarith
    · by_cases hzh : z.re ≤ h
      · have hmin : min h z.re = z.re := min_eq_right hzh
        by_cases hzn : -h ≤ z.re
        · have hceq : c = z.re := by rw [hcdef, hmin, max_eq_right hzn]
          rw [hceq]
          linarith
        · have hzn' : z.re ≤ -h := le_of_lt (lt_of_not_ge hzn)
          have hceq : c = -h := by rw [hcdef, hmin, max_eq_left hzn']
          rw [hceq]
          linarith
      · have hzh' : h ≤ z.re := le_of_lt (lt_of_not_ge hzh)
        have hmin : min h z.re = h := min_eq_left hzh'
        have hceq : c = h := by
          rw [hcdef, hmin, max_eq_right (by linarith)]
        rw [hceq]
        linarith
  have hMain : ∀ n : ℕ, ∃ u : Hilbert, ‖u‖ = 1 ∧
      ‖(H - ((z.re : ℝ) : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) u‖
        < 1 / ((n : ℝ) + 1) := by
    intro n
    have heps : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := finite_box_approx_eigenvector hop c z.re hzmem
      (1 / ((n : ℝ) + 1)) heps
    have hε2 : (0:ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    obtain ⟨a, m, hmN, hblock⟩ := hblk c hc_mem (1 / (2 * ((n : ℝ) + 1))) hε2
      (max n N)
    have hmN' : N ≤ m := le_trans (le_max_right n N) hmN
    have hblk' : ∀ x : Site,
        (x.1 - a.1).natAbs ≤ m →
        (x.2 - a.2).natAbs ≤ m →
        |v x - c| < (1 / ((n : ℝ) + 1)) / 2 := by
      intro x h1 h2
      have hb := hblock x h1 h2
      have heq : 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 := by
        field_simp
      rwa [heq] at hb
    exact hN a m hmN' hblk'
  let u : ℕ → Hilbert := fun n => Classical.choose (hMain n)
  have hu1 : ∀ n, ‖u n‖ = 1 := fun n => (Classical.choose_spec (hMain n)).1
  have hu2 : ∀ n,
      ‖(H - ((z.re : ℝ) : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (u n)‖
        < 1 / ((n : ℝ) + 1) := fun n => (Classical.choose_spec (hMain n)).2
  have htend : Filter.Tendsto
      (fun n => ‖(H - ((z.re : ℝ) : ℂ) • (1 : Hilbert →L[ℂ] Hilbert)) (u n)‖)
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hu2 n)) ?_
    have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) := by
      simpa only using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact hlim
  have hzre : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzim
  rw [hzre]
  exact approx_eigenvalue_mem_spectrum ⟨u, hu1, htend⟩
theorem anderson_spectrum_lower {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧
        spectralInterval h ⊆ spectrum ℂ H := by
  filter_upwards [ae_bounded hh,
    ae_blocks_simultaneous hh (constant_block_occurrence hh)] with v hv hblk
  obtain ⟨H, hop, hsa, -⟩ := anderson_operator_exists_selfAdjoint (h := h) v hv
  exact ⟨H, hop, hsa, spectrum_lower_of_blocks_pos hh v H hop hblk⟩
theorem anderson_spectrum_ae_of_lower
    (hlow : ∀ {h : ℝ}, 0 < h →
      ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
        IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectralInterval h ⊆ spectrum ℂ H)
    {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  filter_upwards [ae_bounded hh, hlow hh] with v hv hlowv
  obtain ⟨H, hop, hsa, hsub⟩ := hlowv
  exact ⟨H, hop, hsa, Set.Subset.antisymm (anderson_spectrum_subset v H hv hop hsa) hsub⟩
theorem spectrum_lower_of_blocks {h : ℝ} (hh : 0 ≤ h)
    (v : Configuration) (H : Hilbert →L[ℂ] Hilbert)
    (hop : IsAndersonOperator v H)
    (hblk : ∀ c ∈ Set.Icc (-h) h, ∀ ε > 0, ∀ N : ℕ,
      ∃ (a : Site) (n : ℕ), N ≤ n ∧
        ∀ x : Site,
          (x.1 - a.1).natAbs ≤ n →
          (x.2 - a.2).natAbs ≤ n →
          |v x - c| < ε) :
    spectralInterval h ⊆ spectrum ℂ H := by
  intro z hz
  obtain ⟨hzim, hzlo, hzhi⟩ := hz
  set c : ℝ := max (-h) (min h z.re) with hcdef
  have hc_mem : c ∈ Set.Icc (-h) h := by
    rw [Set.mem_Icc]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left h z.re)
  have hzmem : z.re ∈ Set.Icc (-4 + c) (4 + c) := by
    rw [Set.mem_Icc]
    constructor
    · by_cases hzh : z.re ≤ h
      · have hmin : min h z.re = z.re := min_eq_right hzh
        by_cases hzn : -h ≤ z.re
        · have hceq : c = z.re := by rw [hcdef, hmin, max_eq_right hzn]
          rw [hceq]
          linarith
        · have hzn' : z.re ≤ -h := le_of_lt (lt_of_not_ge hzn)
          have hceq : c = -h := by rw [hcdef, hmin, max_eq_left hzn']
          rw [hceq]
          linarith
      · have hzh' : h ≤ z.re := le_of_lt (lt_of_not_ge hzh)
        have hmin : min h z.re = h := min_eq_left hzh'
        have hceq : c = h := by
          rw [hcdef, hmin, max_eq_right (by linarith)]
        rw [hceq]
        linarith
    · by_cases hzh : z.re ≤ h
      · have hmin : min h z.re = z.re := min_eq_right hzh
        by_cases hzn : -h ≤ z.re
        · have hceq : c = z.re := by rw [hcdef, hmin, max_eq_right hzn]
          rw [hceq]
          linarith
        · have hzn' : z.re ≤ -h := le_of_lt (lt_of_not_ge hzn)
          have hceq : c = -h := by rw [hcdef, hmin, max_eq_left hzn']
          rw [hceq]
          linarith
      · have hzh' : h ≤ z.re := le_of_lt (lt_of_not_ge hzh)
        have hmin : min h z.re = h := min_eq_left hzh'
        have hceq : c = h := by
          rw [hcdef, hmin, max_eq_right (by linarith)]
        rw [hceq]
        linarith
  have hcrit : ∀ eps : ℝ, 0 < eps → ∃ u : Hilbert, ‖u‖ = 1 ∧
      ‖(algebraMap ℂ (Hilbert →L[ℂ] Hilbert) ((z.re : ℝ) : ℂ) - H) u‖ < eps := by
    intro eps heps
    obtain ⟨N, hN⟩ :=
      finite_box_approx_eigenvector (v := v) (H := H) hop c z.re hzmem eps heps
    obtain ⟨a, n, hnN, hblock⟩ :=
      hblk c hc_mem (eps / 2) (by linarith) N
    have hblk' : ∀ x : Site,
        (x.1 - a.1).natAbs ≤ n →
        (x.2 - a.2).natAbs ≤ n →
        |v x - c| < eps / 2 := hblock
    obtain ⟨u, hu1, hures⟩ := hN a n hnN hblk'
    refine ⟨u, hu1, ?_⟩
    have hneg : (algebraMap ℂ (Hilbert →L[ℂ] Hilbert) ((z.re : ℝ) : ℂ) - H)
        = -(H - (((z.re : ℝ) : ℂ)) • (1 : Hilbert →L[ℂ] Hilbert)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      abel
    rw [hneg, neg_apply, norm_neg]
    exact hures
  have hzre : z = ((z.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hzim
  rw [hzre]
  exact cps_mem_spectrum_of_approx H ((z.re : ℝ) : ℂ) hcrit
theorem anderson_spectrum_ae_sorry_free {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  exact anderson_from_components hh (ae_bounded hh)
    (fun v H hv hop hsa => anderson_spectrum_subset v H hv hop hsa)
    (anderson_spectrum_lower hh)
theorem anderson_spectrum_ae {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  exact anderson_spectrum_ae_sorry_free hh
end PlanarAnderson

end

end OAI
