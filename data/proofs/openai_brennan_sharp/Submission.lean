import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Brennan

def disk : Set ℂ := Metric.ball 0 1

def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U

def Schlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def koebeMap (z : ℂ) : ℂ := z/(1-z)^2

namespace Sharp

def koebeDomain : Set ℂ := koebeMap '' disk

def koebeInverse : ℂ → ℂ := Function.invFunOn koebeMap disk

def areaMoment (f : ℂ → ℂ) (U : Set ℂ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ t) ∂volume

def SharpEndpointStatement : Prop :=
  Schlicht koebeMap ∧
  areaMoment koebeMap disk (-2) = ⊤ ∧
  areaMoment koebeMap disk (2 / 3) = ⊤ ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume ∧
  ¬ IntegrableOn (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume

theorem schlicht_hasDerivAt_koebeMap {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt koebeMap ((1 + z) / (1 - z) ^ 3) z := by
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hden : (1 - z) ^ 2 ≠ 0 := pow_ne_zero 2 hz'
  have hbase := (hasDerivAt_id z).const_sub 1
  have hpow := hbase.pow 2
  have hquot := (hasDerivAt_id z).div hpow (by simpa using hden)
  convert hquot using 1
  · ext w
    rfl
  · simp only [Pi.pow_apply, id_eq]
    field_simp [hz']
    ring
theorem schlicht_deriv_norm {z : ℂ} (hz : z ≠ 1) :
    ‖deriv koebeMap z‖ = ‖1 + z‖ / ‖1 - z‖ ^ 3 := by
  rw [(schlicht_hasDerivAt_koebeMap hz).deriv, norm_div, norm_pow]
theorem schlicht_deriv_rpow_two_thirds {z : ℂ} (hz : z ≠ 1) :
    ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) =
      ‖1 + z‖ ^ (2 / 3 : ℝ) / ‖1 - z‖ ^ 2 := by
  rw [schlicht_deriv_norm hz, Real.div_rpow (norm_nonneg _) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast ‖1 - z‖ 3, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
theorem two_thirds_pointwise_bound {c r : ℝ} {z : ℂ}
    (hc1 : c < 1) (hz1 : z ≠ 1) (hz : z ∈ Metric.ball (c : ℂ) r)
    (hclose : (1 - c) + r ≤ 1 / 2) :
    ‖z - 1‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) := by
  have hzc : ‖z - (c : ℂ)‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  have h2 : ‖(c : ℂ) - 1‖ = 1 - c := by
    rw [show (c : ℂ) - 1 = ((c - 1 : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  have h1 : ‖z - 1‖ ≤ ‖z - (c : ℂ)‖ + ‖(c : ℂ) - 1‖ := by
    have he : z - 1 = (z - (c : ℂ)) + ((c : ℂ) - 1) := by ring
    rw [he]
    exact norm_add_le _ _
  have hz1lt : ‖z - 1‖ < 1 := by
    rw [h2] at h1
    linarith
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hlow : 1 ≤ ‖1 + z‖ := by
    have h1b : ‖1 + z‖ ≥ 2 - ‖1 - z‖ := by
      have he : (1 + z) = (2 : ℂ) - (1 - z) := by ring
      rw [he]
      have := norm_sub_norm_le (2 : ℂ) (1 - z)
      simpa using this
    have h3 : ‖1 - z‖ ≤ 1 := by
      rw [norm_sub_rev 1 z]
      linarith
    linarith
  rw [schlicht_deriv_rpow_two_thirds hz1]
  simp only [norm_sub_rev]
  have hx : (0 : ℝ) < ‖z - 1‖ ^ 2 := by positivity
  have hA : (1 : ℝ) ≤ ‖1 + z‖ ^ (2 / 3 : ℝ) := by
    have h1r := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlow
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    simpa using h1r
  rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_two, inv_eq_one_div,
    div_le_div_iff_of_pos_right hx]
  simpa using hA
theorem koebe_schlicht : Schlicht koebeMap := by
  unfold Schlicht UnivalentOn
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst h
      simp [disk, Metric.mem_ball, dist_eq_norm] at hz
    exact (schlicht_hasDerivAt_koebeMap hz1).differentiableAt.differentiableWithinAt
  · intro z hz w hw h
    have hzlt : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hwlt : ‖w‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hw
    have hz1 : (1 : ℂ) - z ≠ 0 := by
      intro hz0
      have : z = 1 := by linear_combination -hz0
      subst this
      norm_num at hzlt
    have hw1 : (1 : ℂ) - w ≠ 0 := by
      intro hw0
      have : w = 1 := by linear_combination -hw0
      subst this
      norm_num at hwlt
    have hmul : z * (1 - w) ^ 2 = w * (1 - z) ^ 2 :=
      (div_eq_div_iff (pow_ne_zero 2 hz1) (pow_ne_zero 2 hw1)).mp h
    have hfac : (z - w) * (1 - z * w) = 0 := by
      have hdiff : z * (1 - w) ^ 2 - w * (1 - z) ^ 2 = 0 := by
        rw [hmul]
        ring
      linear_combination hdiff
    rcases mul_eq_zero.mp hfac with hzw | hzw
    · exact sub_eq_zero.mp hzw
    · exfalso
      have hone : z * w = 1 := by linear_combination -hzw
      have hnorm : ‖z‖ * ‖w‖ = 1 := by
        rw [← norm_mul, hone, norm_one]
      nlinarith [norm_nonneg z, norm_nonneg w]
  · simp [koebeMap]
  · rw [(schlicht_hasDerivAt_koebeMap (z := 0) (by norm_num)).deriv]
    norm_num
theorem lintegral_eq_top_of_ball_ge {S : Set ℂ} {g : ℂ → ℝ≥0∞} {a : ℂ} (ha : ‖a‖ = 1)
    (hS : ∀ n, Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * a) (((1 : ℝ) / 2) ^ n / 4) ⊆ S)
    (hg_meas : Measurable g) {c : ℝ} (hc : 0 < c)
    (hg : ∀ n, ∀ z ∈ Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * a) (((1 : ℝ) / 2) ^ n / 4),
      ENNReal.ofReal (c * ((5 * ((1 : ℝ) / 2) ^ n / 4) ^ (-2 : ℝ))) ≤ g z) :
    ∫⁻ z in S, g z ∂volume = ⊤ := by
  classical
  set r : ℕ → ℝ := fun n => ((1 : ℝ) / 2) ^ n with hr
  set C : ℕ → ℂ := fun n => ((1 - r n : ℝ) : ℂ) * a with hC
  have hCeq : ∀ n, ((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * a = C n := fun n => by simp [hC, hr]
  have hreq : ∀ n, ((1 : ℝ) / 2) ^ n = r n := fun n => by simp [hr]
  have hr_pos : ∀ n, 0 < r n := fun n => pow_pos (by norm_num) n
  have hr_le : ∀ n, r n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have hr_anti : ∀ {n m : ℕ}, n ≤ m → r m ≤ r n := fun {n m} h =>
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  have hr_half : ∀ n, r (n + 1) = r n / 2 := by
    intro n; simp [hr, pow_succ]; ring
  -- disjointness of the model balls
  have hdisj : Pairwise (fun n m => Disjoint (Metric.ball (C n) (r n / 4))
      (Metric.ball (C m) (r m / 4))) := by
    have hlt : ∀ {n m : ℕ}, n < m → Disjoint (Metric.ball (C n) (r n / 4))
        (Metric.ball (C m) (r m / 4)) := by
      intro n m hnm
      have hrm : r m ≤ r n / 2 := by
        have h1 : r m ≤ r (n + 1) := hr_anti (by omega)
        rw [hr_half] at h1
        exact h1
      have hdist : ‖C n - C m‖ = r n - r m := by
        have hdiff : C n - C m = (((r m - r n : ℝ)) : ℂ) * a := by
          simp only [hC]; push_cast; ring
        rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, mul_one,
          abs_of_nonpos (by linarith [hr_anti (le_of_lt hnm)])]
        ring
      have h4 : r n / 4 + r m / 4 ≤ dist (C n) (C m) := by
        rw [Complex.dist_eq, hdist]
        have := hr_pos n
        linarith
      exact Metric.ball_disjoint_ball h4
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hlt h
    · exact (hlt h).symm
  -- the per-ball constant is independent of `n`
  have hkey : ∀ n, c * (5 * r n / 4) ^ (-2 : ℝ) * ((r n / 4) ^ 2 * Real.pi)
      = c * (Real.pi / 25) := by
    intro n
    have hrne : r n ≠ 0 := ne_of_gt (hr_pos n)
    have h5 : (0 : ℝ) < 5 * r n / 4 := by positivity
    have hsq : (5 * r n / 4) ^ 2 = 25 * ((r n / 4) ^ 2) := by ring
    rw [Real.rpow_neg (le_of_lt h5), Real.rpow_two, hsq]
    field_simp
  have hvol : ∀ n, volume (Metric.ball (C n) (r n / 4))
      = ENNReal.ofReal ((r n / 4) ^ 2 * Real.pi) := by
    intro n
    rw [Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_coe_nnreal (p := NNReal.pi), ← ENNReal.ofReal_mul (by positivity)]
    norm_num [NNReal.coe_real_pi]
  have hball_int : ∀ n, ENNReal.ofReal (c * (Real.pi / 25)) ≤
      ∫⁻ z in Metric.ball (C n) (r n / 4), g z ∂volume := by
    intro n
    have hstep : ENNReal.ofReal (c * (Real.pi / 25)) =
        ENNReal.ofReal (c * (5 * r n / 4) ^ (-2 : ℝ)) * volume (Metric.ball (C n) (r n / 4)) := by
      rw [hvol n, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact (hkey n).symm
    rw [hstep, ← setLIntegral_const]
    refine setLIntegral_mono hg_meas (fun z hz => ?_)
    exact hg n z (by rw [hCeq n, hreq n]; exact hz)
  have hmain : (∑' n : ℕ, ENNReal.ofReal (c * (Real.pi / 25))) ≤ ∫⁻ z in S, g z ∂volume := by
    have h1 : (∑' n : ℕ, ENNReal.ofReal (c * (Real.pi / 25)))
        ≤ ∑' n : ℕ, ∫⁻ z in Metric.ball (C n) (r n / 4), g z ∂volume :=
      ENNReal.tsum_le_tsum (fun n => hball_int n)
    have h2 : (∑' n : ℕ, ∫⁻ z in Metric.ball (C n) (r n / 4), g z ∂volume)
        = ∫⁻ z in (⋃ n, Metric.ball (C n) (r n / 4)), g z ∂volume :=
      (lintegral_iUnion (fun n => measurableSet_ball) hdisj g).symm
    have h3 : (∫⁻ z in (⋃ n, Metric.ball (C n) (r n / 4)), g z ∂volume)
        ≤ ∫⁻ z in S, g z ∂volume := by
      refine lintegral_mono_set ?_
      refine iUnion_subset (fun n z hz => hS n ?_)
      rwa [hCeq n, hreq n]
    calc (∑' n : ℕ, ENNReal.ofReal (c * (Real.pi / 25)))
        ≤ ∑' n : ℕ, ∫⁻ z in Metric.ball (C n) (r n / 4), g z ∂volume := h1
      _ = ∫⁻ z in (⋃ n, Metric.ball (C n) (r n / 4)), g z ∂volume := h2
      _ ≤ ∫⁻ z in S, g z ∂volume := h3
  have htop : (∑' n : ℕ, ENNReal.ofReal (c * (Real.pi / 25))) = ⊤ := by
    have hne : ENNReal.ofReal (c * (Real.pi / 25)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    exact ENNReal.tsum_const_eq_top_of_ne_zero hne
  rw [htop] at hmain
  exact top_le_iff.mp hmain
theorem koebeModel_ball_subset_disk {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) :
    Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * a) (((1 : ℝ) / 2) ^ n / 4) ⊆ disk := by
  intro z hz
  have hρ : (0 : ℝ) < ((1 : ℝ) / 2) ^ n := pow_pos (by norm_num) n
  have hlt : ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ < ((1 : ℝ) / 2) ^ n / 4 := by
    simpa [Metric.mem_ball, Complex.dist_eq] using hz
  have hcn : ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ = 1 - ((1 : ℝ) / 2) ^ n := by
    have h1 : (0 : ℝ) ≤ 1 - ((1 : ℝ) / 2) ^ n := by
      have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (n := n)
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1, ha, mul_one]
  have htri : ‖z‖ ≤ ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖
      + ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ := by
    have hz' : (z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a)
        + (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a = z := by ring
    calc ‖z‖ = ‖(z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a)
        + (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ := by rw [hz']
      _ ≤ _ := norm_add_le _ _
  rw [disk, Metric.mem_ball, Complex.dist_eq, sub_zero]
  linarith
theorem koebeModel_norm_sub_le {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * a) (((1 : ℝ) / 2) ^ n / 4)) :
    ‖z - a‖ ≤ 5 * ((1 : ℝ) / 2) ^ n / 4 := by
  have hρ : (0 : ℝ) < ((1 : ℝ) / 2) ^ n := pow_pos (by norm_num) n
  have hlt : ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ < ((1 : ℝ) / 2) ^ n / 4 := by
    simpa [Metric.mem_ball, Complex.dist_eq] using hz
  have h3 : ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a‖ = ((1 : ℝ) / 2) ^ n := by
    have hc' : (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a
        = ((-(((1 : ℝ) / 2) ^ n) : ℝ) : ℂ) * a := by push_cast; ring
    rw [hc', norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, mul_one,
      abs_of_nonpos (by linarith)]
    ring
  have htri : ‖z - a‖ ≤ ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖
      + ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a‖ := by
    have hz' : (z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a)
        + ((((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a) = z - a := by ring
    calc ‖z - a‖ = ‖(z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a)
        + ((((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a)‖ := by rw [hz']
      _ ≤ _ := norm_add_le _ _
  linarith
theorem lintegral_norm_sub_unit_top :
    ∀ (a : ℂ), ‖a‖ = 1 →
      ∫⁻ z in OAI.Brennan.disk, ENNReal.ofReal (‖z - a‖ ^ (-2 : ℝ)) ∂MeasureTheory.volume = ⊤ := by
  intro a ha
  refine lintegral_eq_top_of_ball_ge (S := disk) (g := fun z => ENNReal.ofReal (‖z - a‖ ^ (-2 : ℝ)))
    ha (fun n => koebeModel_ball_subset_disk ha n) (by fun_prop) (c := 1) (by norm_num) ?_
  intro n z hz
  have hρ : (0 : ℝ) < ((1 : ℝ) / 2) ^ n := pow_pos (by norm_num) n
  have hlt : ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ < ((1 : ℝ) / 2) ^ n / 4 := by
    simpa [Metric.mem_ball, Complex.dist_eq] using hz
  have hcn : ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a‖ = ((1 : ℝ) / 2) ^ n := by
    have hc' : (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a
        = ((-(((1 : ℝ) / 2) ^ n) : ℝ) : ℂ) * a := by push_cast; ring
    rw [hc', norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, mul_one,
      abs_of_nonpos (by linarith)]
    ring
  have hne : z - a ≠ 0 := by
    intro h0
    have h0' : ‖z - a‖ = 0 := by rw [h0, norm_zero]
    have htri : ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a‖
        ≤ ‖z - a‖ + ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ := by
      have hz' : (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a
          = (z - a) - (z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a) := by ring
      calc ‖(((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a - a‖
          = ‖(z - a) - (z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a)‖ := by rw [hz']
        _ ≤ ‖z - a‖ + ‖z - (((1 - ((1 : ℝ) / 2) ^ n : ℝ)) : ℂ) * a‖ := norm_sub_le _ _
    linarith
  have hpos : (0 : ℝ) < ‖z - a‖ := norm_pos_iff.mpr hne
  have hle : ‖z - a‖ ≤ 5 * ((1 : ℝ) / 2) ^ n / 4 := koebeModel_norm_sub_le ha n hz
  have hstep : (5 * ((1 : ℝ) / 2) ^ n / 4) ^ (-2 : ℝ) ≤ ‖z - a‖ ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have := ENNReal.ofReal_le_ofReal hstep
  simpa [one_mul] using this
theorem deriv_koebeInverse :
    ∀ w ∈ koebeDomain,
      deriv koebeInverse w = (1 - koebeInverse w) ^ 3 / (1 + koebeInverse w) := by
  intro w hw
  obtain ⟨z, hz_disk, hz_eq⟩ := hw
  have hz_norm_lt : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz_disk
  have hz_ne_one : z ≠ 1 := by
    intro h
    subst h
    norm_num at hz_norm_lt
  have hz_ne_neg_one : (1 : ℂ) + z ≠ 0 := by
    intro h
    have hz : z = -1 := by linear_combination h
    subst hz
    rw [norm_neg, norm_one] at hz_norm_lt
    norm_num at hz_norm_lt
  have hz1 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz_ne_one.symm
  have hf'_ne : (1 + z) / (1 - z) ^ 3 ≠ 0 :=
    div_ne_zero hz_ne_neg_one (pow_ne_zero 3 hz1)
  have hcont : ContinuousAt (fun y : ℂ => (1 + y) / (1 - y) ^ 3) z := by
    exact (continuousAt_const.add continuousAt_id).div
      ((continuousAt_const.sub continuousAt_id).pow 3) (by simpa using pow_ne_zero 3 hz1)
  have hstrict : HasStrictDerivAt koebeMap ((1 + z) / (1 - z) ^ 3) z := by
    refine hasStrictDerivAt_of_hasDerivAt_of_continuousAt (f := koebeMap)
      (f' := fun y : ℂ => (1 + y) / (1 - y) ^ 3) (x := z) ?_ hcont
    filter_upwards [Metric.isOpen_ball.mem_nhds hz_disk] with y hy
    apply schlicht_hasDerivAt_koebeMap
    intro h
    subst h
    simp [Metric.mem_ball, dist_eq_norm] at hy
  have hleft : ∀ᶠ x in 𝓝 z, koebeInverse (koebeMap x) = x := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz_disk] with x hx
    exact koebe_schlicht.1.2.leftInvOn_invFunOn hx
  have hstrict_inv : HasStrictDerivAt koebeInverse ((1 + z) / (1 - z) ^ 3)⁻¹ (koebeMap z) :=
    hstrict.to_local_left_inverse hf'_ne hleft
  have hderiv : deriv koebeInverse w = ((1 + z) / (1 - z) ^ 3)⁻¹ := by
    rw [← hz_eq]
    exact hstrict_inv.hasDerivAt.deriv
  have hz_inv : koebeInverse w = z := by
    rw [← hz_eq]
    exact koebe_schlicht.1.2.leftInvOn_invFunOn hz_disk
  rw [hderiv, hz_inv, inv_div]
theorem two_thirds_pointwise_bound_near_one {z : ℂ} (hz : z ∈ disk)
    (hclose : ‖z - 1‖ ≤ 1 / 2) :
    ‖z - 1‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) := by
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    simp [disk, Metric.mem_ball, dist_eq_norm] at hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have h1z : ‖1 - z‖ ≤ 1 / 2 := by simpa [norm_sub_rev] using hclose
  have hlow : 1 ≤ ‖1 + z‖ := by
    have he : (1 + z) = (2 : ℂ) - (1 - z) := by ring
    have h1b : ‖1 + z‖ ≥ 2 - ‖1 - z‖ := by
      rw [he]
      have := norm_sub_norm_le (2 : ℂ) (1 - z)
      simpa using this
    linarith
  rw [schlicht_deriv_rpow_two_thirds hz1]
  simp only [norm_sub_rev]
  have hx : (0 : ℝ) < ‖z - 1‖ ^ 2 := by positivity
  have hA : (1 : ℝ) ≤ ‖1 + z‖ ^ (2 / 3 : ℝ) := by
    have h1r := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlow
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    simpa using h1r
  rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_two, inv_eq_one_div,
    div_le_div_iff_of_pos_right hx]
  simpa using hA
theorem areaMoment_two_thirds_top :
    areaMoment koebeMap disk (2 / 3) = ⊤ := by
  unfold areaMoment
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z - 1‖ ^ (-2 : ℝ)) with hf
  set B : Set ℂ := Metric.closedBall (1 : ℂ) (1 / 2) with hB
  set U : Set ℂ := disk ∩ B with hU
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact measurableSet_closedBall
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact measurableSet_ball.inter hBmeas
  have hmemB : ∀ z : ℂ, z ∈ B ↔ ‖z - 1‖ ≤ 1 / 2 := by
    intro z
    rw [hB, Metric.mem_closedBall, Complex.dist_eq]
  have hmodel : ∫⁻ z in disk, f z ∂volume = ⊤ := by
    rw [hf]
    simpa using lintegral_norm_sub_unit_top (1 : ℂ) (by simp)
  have hsplit : (∫⁻ z in disk ∩ B, f z ∂volume) + ∫⁻ z in disk \ B, f z ∂volume
      = ∫⁻ z in disk, f z ∂volume :=
    lintegral_inter_add_sdiff f disk hBmeas
  have hcompl : ∫⁻ z in disk \ B, f z ∂volume < ⊤ := by
    have hle : ∫⁻ z in disk \ B, f z ∂volume
        ≤ ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume := by
      refine setLIntegral_mono' (measurableSet_ball.diff hBmeas) ?_
      intro z hz
      have hzB : z ∉ B := hz.2
      have hfar : (1 / 2 : ℝ) < ‖z - 1‖ := by
        by_contra hcon
        exact hzB ((hmemB z).mpr (le_of_not_gt hcon))
      rw [hf]
      have hstep : ‖z - 1‖ ^ (-2 : ℝ) ≤ (4 : ℝ) := by
        have h1 : ‖z - 1‖ ^ (-2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_lt hfar) (by norm_num)
        have h2 : (1 / 2 : ℝ) ^ (-2 : ℝ) = 4 := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_two]
          norm_num
        linarith [h2 ▸ h1]
      calc ENNReal.ofReal (‖z - 1‖ ^ (-2 : ℝ)) ≤ ENNReal.ofReal 4 :=
            ENNReal.ofReal_le_ofReal hstep
        _ = (4 : ℝ≥0∞) := by norm_num
    have hvol : ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume
        = 4 * volume (disk \ B) := setLIntegral_const _ _
    have hfinite : volume (disk \ B) < ⊤ := by
      have hmono : volume (disk \ B) ≤ volume disk :=
        MeasureTheory.measure_mono Set.sdiff_subset
      have hvdisk : volume disk = ENNReal.ofReal Real.pi := by
        rw [disk, Complex.volume_ball]
        rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1)]
        rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi)]
        rw [← ENNReal.ofReal_mul (by positivity)]
        norm_num [NNReal.coe_real_pi]
      rw [hvdisk] at hmono
      exact lt_of_le_of_lt hmono ENNReal.ofReal_lt_top
    calc ∫⁻ z in disk \ B, f z ∂volume
        ≤ ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume := hle
      _ = 4 * volume (disk \ B) := hvol
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hfinite
  have hUtop : ∫⁻ z in U, f z ∂volume = ⊤ := by
    have hsum : (∫⁻ z in U, f z ∂volume) + ∫⁻ z in disk \ B, f z ∂volume = ⊤ := by
      rw [show U = disk ∩ B from hU]
      rw [hsplit, hmodel]
    rcases ENNReal.add_eq_top.mp hsum with h | h
    · exact h
    · exact absurd h (ne_of_lt hcompl)
  have hdom : ∫⁻ z in U, f z ∂volume ≤ ∫⁻ z in disk,
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
    calc ∫⁻ z in U, f z ∂volume
        ≤ ∫⁻ z in U, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
          refine setLIntegral_mono' hUmeas ?_
          intro z hz
          rw [hf]
          exact ENNReal.ofReal_le_ofReal
            (two_thirds_pointwise_bound_near_one (by rw [hU] at hz; exact hz.1)
              (hmemB z |>.mp (by rw [hU] at hz; exact hz.2)))
      _ ≤ ∫⁻ z in disk, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
          refine lintegral_mono_set ?_
          rw [hU]
          exact Set.inter_subset_left
  have htop : ∫⁻ z in disk,
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume = ⊤ := by
    have hle : ⊤ ≤ ∫⁻ z in disk,
        ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
      rw [← hUtop]
      exact hdom
    exact top_le_iff.mp hle
  exact htop
theorem neg_two_uniform_bound {n : ℕ} {z : ℂ}
    (hz : z ∈ Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * (-1 : ℂ))
      (((1 : ℝ) / 2) ^ n / 4)) :
    (3 / 4 : ℝ) ^ 6 * (5 * ((1 : ℝ) / 2) ^ n / 4) ^ (-2 : ℝ) ≤
      ‖deriv koebeMap z‖ ^ (-2 : ℝ) := by
  set r : ℝ := ((1 : ℝ) / 2) ^ n with hr
  have hrpos : 0 < r := pow_pos (by norm_num) n
  have hrle : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hzdisk : z ∈ disk :=
    koebeModel_ball_subset_disk (a := (-1 : ℂ)) (by norm_num) n (by simpa [r] using hz)
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hzdisk
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    norm_num at hznorm
  have hzneg1 : z ≠ -1 := by
    intro h
    subst h
    rw [norm_neg, norm_one] at hznorm
    norm_num at hznorm
  have hA_le : ‖1 + z‖ ≤ 5 * r / 4 := by
    have h := koebeModel_norm_sub_le (a := (-1 : ℂ)) (by norm_num) n (by simpa [r] using hz)
    simpa [r, add_comm] using h
  have hA_pos : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hzneg1
    linear_combination h
  have hB_ge : (3 / 4 : ℝ) ≤ ‖1 - z‖ := by
    have htri : ‖(2 : ℂ)‖ ≤ ‖1 - z‖ + ‖1 + z‖ := by
      calc ‖(2 : ℂ)‖ = ‖(1 - z) + (1 + z)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at htri
    linarith
  have hB_pos : 0 < ‖1 - z‖ := lt_of_lt_of_le (by norm_num) hB_ge
  have hA_sq_pos : 0 < ‖1 + z‖ ^ 2 := by positivity
  have hA_sq_le : ‖1 + z‖ ^ 2 ≤ (5 * r / 4) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hA_le 2
  have hB6 : (3 / 4 : ℝ) ^ 6 ≤ ‖1 - z‖ ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hB_ge 6
  have hchain : (3 / 4 : ℝ) ^ 6 / (5 * r / 4) ^ 2 ≤
      ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 := by
    calc (3 / 4 : ℝ) ^ 6 / (5 * r / 4) ^ 2
        ≤ ‖1 - z‖ ^ 6 / (5 * r / 4) ^ 2 :=
          div_le_div_of_nonneg_right hB6 (sq_nonneg _)
      _ ≤ ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) 6) hA_sq_pos hA_sq_le
  have hneg : ‖deriv koebeMap z‖ ^ (-2 : ℝ) = ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 := by
    rw [schlicht_deriv_norm hz1]
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two,
      div_pow]
    rw [inv_div]
    congr 1
    rw [show (‖1 - z‖ ^ 3) ^ 2 = ‖1 - z‖ ^ 6 by ring]
  rw [hneg]
  have hscale : (5 * r / 4) ^ (-2 : ℝ) = ((5 * r / 4) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hscale, div_eq_mul_inv]
  exact hchain
theorem areaMoment_neg_two_top : areaMoment koebeMap disk (-2) = ⊤ := by
  have h := lintegral_eq_top_of_ball_ge (S := disk)
    (g := fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)))
    (a := (-1 : ℂ)) (by norm_num)
    (fun n => koebeModel_ball_subset_disk (a := (-1 : ℂ)) (by norm_num) n)
    (by fun_prop) (c := (3 / 4 : ℝ) ^ 6) (by positivity)
    (fun n z hz => ENNReal.ofReal_le_ofReal (neg_two_uniform_bound hz))
  simpa [areaMoment] using h
theorem inv4cov_det_real_complex_smul_one (c : ℂ) :
    ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  rw [← Complex.restrictScalars_toSpanSingleton c]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
theorem inv4cov_abs_det_fderiv_koebeMap {z : ℂ} (hz : z ≠ 1) :
    |(fderiv ℝ koebeMap z).det| = ‖deriv koebeMap z‖ ^ 2 := by
  have hd := (schlicht_hasDerivAt_koebeMap hz).complexToReal_fderiv
  rw [hd.fderiv]
  rw [inv4cov_det_real_complex_smul_one]
  rw [← (schlicht_hasDerivAt_koebeMap hz).deriv]
  rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
theorem inv4cov_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    koebeInverse (koebeMap z) = z := by
  exact koebe_schlicht.1.2.leftInvOn_invFunOn.eq hz
theorem inv4cov_deriv_inv_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    deriv koebeInverse (koebeMap z) = (1 - z) ^ 3 / (1 + z) := by
  have hki := inv4cov_koebeInverse_koebeMap hz
  have hmem : koebeMap z ∈ koebeDomain := ⟨z, hz, rfl⟩
  rw [deriv_koebeInverse (koebeMap z) hmem, hki]
theorem inv4cov_norm_deriv_inv_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeInverse (koebeMap z)‖ ^ (4 : ℝ) =
      ‖1 - z‖ ^ 12 / ‖1 + z‖ ^ 4 := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    norm_num at hznorm
  rw [inv4cov_deriv_inv_koebeInverse_koebeMap hz]
  rw [norm_div, norm_pow]
  rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]
  rw [show (‖1 - z‖ ^ 3) ^ 4 = ‖1 - z‖ ^ 12 by ring]
theorem inv4cov_jacobian_arith {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A / B ^ 3) ^ 2 * (B ^ 12 / A ^ 4) = (A / B ^ 3) ^ (-2 : ℝ) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  field_simp [hA.ne', hB.ne']
theorem inv4cov_real_jacobian_weight {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeMap z‖ ^ 2 *
        (‖1 - z‖ ^ 12 / ‖1 + z‖ ^ 4) =
      ‖deriv koebeMap z‖ ^ (-2 : ℝ) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    norm_num at hznorm
  have hB : 0 < ‖1 - z‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hz1.symm
  have hA : 0 < ‖1 + z‖ := by
    rw [norm_pos_iff]
    intro h
    have hz' : z = -1 := by linear_combination h
    subst hz'
    rw [norm_neg, norm_one] at hznorm
    norm_num at hznorm
  rw [schlicht_deriv_norm hz1]
  exact inv4cov_jacobian_arith hA hB
theorem inv4cov_jacobian_weight_mul {z : ℂ} (hz : z ∈ disk) :
    ENNReal.ofReal |(fderiv ℝ koebeMap z).det| *
        ENNReal.ofReal (‖deriv koebeInverse (koebeMap z)‖ ^ (4 : ℝ)) =
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    norm_num at hznorm
  rw [← ENNReal.ofReal_mul (abs_nonneg (fderiv ℝ koebeMap z).det)]
  rw [inv4cov_abs_det_fderiv_koebeMap hz1]
  rw [inv4cov_norm_deriv_inv_koebeInverse_koebeMap hz]
  exact congrArg ENNReal.ofReal (inv4cov_real_jacobian_weight hz)
theorem inv4_cov_lintegral :
    ∫⁻ w in OAI.Brennan.Sharp.koebeDomain,
      ENNReal.ofReal (‖deriv OAI.Brennan.Sharp.koebeInverse w‖ ^ (4 : ℝ)) ∂MeasureTheory.volume
    = ∫⁻ z in OAI.Brennan.disk,
      ENNReal.ofReal (‖deriv OAI.Brennan.koebeMap z‖ ^ (-2 : ℝ)) ∂MeasureTheory.volume := by
  let g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖deriv koebeInverse w‖ ^ (4 : ℝ))
  have hs : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  let f' : ℂ → ℂ →L[ℝ] ℂ := fun z => deriv koebeMap z • (1 : ℂ →L[ℝ] ℂ)
  have hf' : ∀ z ∈ disk, HasFDerivWithinAt koebeMap (f' z) disk z := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hz1 : z ≠ 1 := by
      intro h
      subst h
      norm_num at hznorm
    simpa [f', (schlicht_hasDerivAt_koebeMap hz1).deriv] using
      ((schlicht_hasDerivAt_koebeMap hz1).complexToReal_fderiv).hasFDerivWithinAt
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) (s := disk) (f := koebeMap) (f' := f') hs hf' koebe_schlicht.1.2 g
  have hcongr : ∫⁻ z in disk,
      ENNReal.ofReal |(f' z).det| * g (koebeMap z) ∂volume =
      ∫⁻ z in disk, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) ∂volume :=
    MeasureTheory.setLIntegral_congr_fun hs (fun z hz => by
      have hznorm : ‖z‖ < 1 := by
        simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
      have hz1 : z ≠ 1 := by
        intro h
        subst h
        norm_num at hznorm
      dsimp [f', g]
      rw [inv4cov_det_real_complex_smul_one, Complex.normSq_eq_norm_sq,
        abs_of_nonneg (sq_nonneg _), inv4cov_norm_deriv_inv_koebeInverse_koebeMap hz,
        ← ENNReal.ofReal_mul (sq_nonneg ‖deriv koebeMap z‖)]
      exact congrArg ENNReal.ofReal (inv4cov_real_jacobian_weight hz))
  calc
    ∫⁻ w in koebeDomain,
        ENNReal.ofReal (‖deriv koebeInverse w‖ ^ (4 : ℝ)) ∂volume
        = ∫⁻ z in disk,
            ENNReal.ofReal |(f' z).det| * g (koebeMap z) ∂volume := by
          change ∫⁻ w in koebeMap '' disk, g w ∂volume = _
          exact hcov
    _ = ∫⁻ z in disk,
            ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) ∂volume := hcongr
theorem inv43_deriv_rpow_two_thirds {z : ℂ} (hz : z ≠ 1) :
    ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) =
      ‖1 + z‖ ^ (2 / 3 : ℝ) / ‖1 - z‖ ^ 2 := by
  rw [schlicht_deriv_norm hz, Real.div_rpow (norm_nonneg _) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast ‖1 - z‖ 3, ← Real.rpow_mul (norm_nonneg _)]
  norm_num
theorem inv43_two_thirds_pointwise_bound_near_one {z : ℂ} (hz : z ∈ disk)
    (hclose : ‖z - 1‖ ≤ 1 / 2) :
    ‖z - 1‖ ^ (-2 : ℝ) ≤ ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) := by
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    simp [disk, Metric.mem_ball, dist_eq_norm] at hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have h1z : ‖1 - z‖ ≤ 1 / 2 := by simpa [norm_sub_rev] using hclose
  have hlow : 1 ≤ ‖1 + z‖ := by
    have he : (1 + z) = (2 : ℂ) - (1 - z) := by ring
    have h1b : ‖1 + z‖ ≥ 2 - ‖1 - z‖ := by
      rw [he]
      have := norm_sub_norm_le (2 : ℂ) (1 - z)
      simpa using this
    linarith
  rw [inv43_deriv_rpow_two_thirds hz1]
  simp only [norm_sub_rev]
  have hx : (0 : ℝ) < ‖z - 1‖ ^ 2 := by positivity
  have hA : (1 : ℝ) ≤ ‖1 + z‖ ^ (2 / 3 : ℝ) := by
    have h1r := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hlow
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
    simpa using h1r
  rw [Real.rpow_neg (le_of_lt hpos), Real.rpow_two, inv_eq_one_div,
    div_le_div_iff_of_pos_right hx]
  simpa using hA
theorem inv43_areaMoment_two_thirds_top :
    areaMoment koebeMap disk (2 / 3) = ⊤ := by
  unfold areaMoment
  set f : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖z - 1‖ ^ (-2 : ℝ)) with hf
  set B : Set ℂ := Metric.closedBall (1 : ℂ) (1 / 2) with hB
  set U : Set ℂ := disk ∩ B with hU
  have hBmeas : MeasurableSet B := by
    rw [hB]
    exact measurableSet_closedBall
  have hUmeas : MeasurableSet U := by
    rw [hU]
    exact measurableSet_ball.inter hBmeas
  have hmemB : ∀ z : ℂ, z ∈ B ↔ ‖z - 1‖ ≤ 1 / 2 := by
    intro z
    rw [hB, Metric.mem_closedBall, Complex.dist_eq]
  have hmodel : ∫⁻ z in disk, f z ∂volume = ⊤ := by
    rw [hf]
    simpa using lintegral_norm_sub_unit_top (1 : ℂ) (by simp)
  have hsplit : (∫⁻ z in disk ∩ B, f z ∂volume) + ∫⁻ z in disk \ B, f z ∂volume
      = ∫⁻ z in disk, f z ∂volume :=
    lintegral_inter_add_sdiff f disk hBmeas
  have hcompl : ∫⁻ z in disk \ B, f z ∂volume < ⊤ := by
    have hle : ∫⁻ z in disk \ B, f z ∂volume
        ≤ ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume := by
      refine setLIntegral_mono' (measurableSet_ball.diff hBmeas) ?_
      intro z hz
      have hzB : z ∉ B := hz.2
      have hfar : (1 / 2 : ℝ) < ‖z - 1‖ := by
        by_contra hcon
        exact hzB ((hmemB z).mpr (le_of_not_gt hcon))
      rw [hf]
      have hstep : ‖z - 1‖ ^ (-2 : ℝ) ≤ (4 : ℝ) := by
        have h1 : ‖z - 1‖ ^ (-2 : ℝ) ≤ (1 / 2 : ℝ) ^ (-2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_lt hfar) (by norm_num)
        have h2 : (1 / 2 : ℝ) ^ (-2 : ℝ) = 4 := by
          rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.rpow_two]
          norm_num
        linarith [h2 ▸ h1]
      calc ENNReal.ofReal (‖z - 1‖ ^ (-2 : ℝ)) ≤ ENNReal.ofReal 4 :=
            ENNReal.ofReal_le_ofReal hstep
        _ = (4 : ℝ≥0∞) := by norm_num
    have hvol : ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume
        = 4 * volume (disk \ B) := setLIntegral_const _ _
    have hfinite : volume (disk \ B) < ⊤ := by
      have hmono : volume (disk \ B) ≤ volume disk :=
        MeasureTheory.measure_mono Set.sdiff_subset
      have hvdisk : volume disk = ENNReal.ofReal Real.pi := by
        rw [disk, Complex.volume_ball]
        rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1)]
        rw [← ENNReal.ofReal_coe_nnreal (p := NNReal.pi)]
        rw [← ENNReal.ofReal_mul (by positivity)]
        norm_num [NNReal.coe_real_pi]
      rw [hvdisk] at hmono
      exact lt_of_le_of_lt hmono ENNReal.ofReal_lt_top
    calc ∫⁻ z in disk \ B, f z ∂volume
        ≤ ∫⁻ z in disk \ B, (4 : ℝ≥0∞) ∂volume := hle
      _ = 4 * volume (disk \ B) := hvol
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hfinite
  have hUtop : ∫⁻ z in U, f z ∂volume = ⊤ := by
    have hsum : (∫⁻ z in U, f z ∂volume) + ∫⁻ z in disk \ B, f z ∂volume = ⊤ := by
      rw [show U = disk ∩ B from hU]
      rw [hsplit, hmodel]
    rcases ENNReal.add_eq_top.mp hsum with h | h
    · exact h
    · exact absurd h (ne_of_lt hcompl)
  have hdom : ∫⁻ z in U, f z ∂volume ≤ ∫⁻ z in disk,
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
    calc ∫⁻ z in U, f z ∂volume
        ≤ ∫⁻ z in U, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
          refine setLIntegral_mono' hUmeas ?_
          intro z hz
          rw [hf]
          exact ENNReal.ofReal_le_ofReal
            (inv43_two_thirds_pointwise_bound_near_one (by rw [hU] at hz; exact hz.1)
              (hmemB z |>.mp (by rw [hU] at hz; exact hz.2)))
      _ ≤ ∫⁻ z in disk, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
          refine lintegral_mono_set ?_
          rw [hU]
          exact Set.inter_subset_left
  have htop : ∫⁻ z in disk,
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume = ⊤ := by
    have hle : ⊤ ≤ ∫⁻ z in disk,
        ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume := by
      rw [← hUtop]
      exact hdom
    exact top_le_iff.mp hle
  exact htop
lemma inv43_det_real_complex_smul_one (c : ℂ) :
    ((c • (1 : ℂ →L[ℝ] ℂ)) : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  rw [← Complex.restrictScalars_toSpanSingleton c]
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]
lemma inv43_abs_det_fderiv_koebeMap {z : ℂ} (hz : z ≠ 1) :
    |(fderiv ℝ koebeMap z).det| = ‖deriv koebeMap z‖ ^ 2 := by
  have hd := (schlicht_hasDerivAt_koebeMap hz).complexToReal_fderiv
  rw [hd.fderiv]
  rw [inv43_det_real_complex_smul_one]
  rw [← (schlicht_hasDerivAt_koebeMap hz).deriv]
  rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
lemma inv43_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    koebeInverse (koebeMap z) = z := by
  exact koebe_schlicht.1.2.leftInvOn_invFunOn.eq hz
lemma deriv_inv43_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    deriv koebeInverse (koebeMap z) = (1 - z) ^ 3 / (1 + z) := by
  have hki := inv43_koebeInverse_koebeMap hz
  have hmem : koebeMap z ∈ koebeDomain := ⟨z, hz, rfl⟩
  rw [deriv_koebeInverse (koebeMap z) hmem, hki]
lemma norm_deriv_inv43_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeInverse (koebeMap z)‖ ^ (4 / 3 : ℝ) =
      ‖1 - z‖ ^ 4 / ‖1 + z‖ ^ (4 / 3 : ℝ) := by
  rw [deriv_inv43_koebeInverse_koebeMap hz]
  rw [norm_div, norm_pow]
  rw [Real.div_rpow (by positivity : (0:ℝ) ≤ ‖1 - z‖ ^ 3)
    (by positivity : (0:ℝ) ≤ ‖1 + z‖) (4 / 3 : ℝ)]
  rw [show (‖1 - z‖ ^ 3) ^ (4 / 3 : ℝ) = ‖1 - z‖ ^ 4 by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ‖1 - z‖)]
    norm_num]
lemma inv43_real_jacobian_weight {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeMap z‖ ^ 2 *
        (‖1 - z‖ ^ 4 / ‖1 + z‖ ^ (4 / 3 : ℝ)) =
      ‖deriv koebeMap z‖ ^ (2 / 3 : ℝ) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hznorm
  have hB : ‖1 - z‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr hz1.symm
  rw [schlicht_deriv_norm hz1]
  by_cases hA : ‖1 + z‖ = 0
  · simp [hA, Real.zero_rpow]
  · have hApos : 0 < ‖1 + z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
    rw [Real.div_rpow (by positivity : (0:ℝ) ≤ ‖1 + z‖)
      (by positivity : (0:ℝ) ≤ ‖1 - z‖ ^ 3) (2 / 3 : ℝ)]
    have hBexp : (‖1 - z‖ ^ 3) ^ (2 / 3 : ℝ) = ‖1 - z‖ ^ 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [hBexp]
    have hAexp : ‖1 + z‖ ^ 2 = ‖1 + z‖ ^ (4 / 3 : ℝ) * ‖1 + z‖ ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hApos]
      norm_num
    rw [div_pow, hAexp]
    field_simp [hA, hB]
lemma inv43_jacobian_weight_mul {z : ℂ} (hz : z ∈ disk) :
    ENNReal.ofReal |(fderiv ℝ koebeMap z).det| *
        ENNReal.ofReal (‖deriv koebeInverse (koebeMap z)‖ ^ (4 / 3 : ℝ)) =
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hznorm
  rw [← ENNReal.ofReal_mul (abs_nonneg (fderiv ℝ koebeMap z).det)]
  rw [inv43_abs_det_fderiv_koebeMap hz1]
  rw [norm_deriv_inv43_koebeInverse_koebeMap hz]
  exact congrArg ENNReal.ofReal (inv43_real_jacobian_weight hz)
theorem inv_deriv_four_thirds_not_integrable :
    ¬ MeasureTheory.IntegrableOn
      (fun z => ‖deriv koebeInverse z‖ ^ (4 / 3 : ℝ)) koebeDomain volume := by
  let g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖deriv koebeInverse w‖ ^ (4 / 3 : ℝ))
  have hs : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  let f' : ℂ → ℂ →L[ℝ] ℂ := fun z => deriv koebeMap z • (1 : ℂ →L[ℝ] ℂ)
  have hf' : ∀ z ∈ disk, HasFDerivWithinAt koebeMap (f' z) disk z := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hznorm
    simpa [f', (schlicht_hasDerivAt_koebeMap hz1).deriv] using
      ((schlicht_hasDerivAt_koebeMap hz1).complexToReal_fderiv).hasFDerivWithinAt
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) (s := disk) (f := koebeMap) (f' := f') hs hf' koebe_schlicht.1.2 g
  have hweight : ∀ z ∈ disk,
      ENNReal.ofReal |(f' z).det| * g (koebeMap z) =
        ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hznorm
    dsimp [f', g]
    rw [inv43_det_real_complex_smul_one, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg _), norm_deriv_inv43_koebeInverse_koebeMap hz,
      ← ENNReal.ofReal_mul (sq_nonneg ‖deriv koebeMap z‖)]
    exact congrArg ENNReal.ofReal (inv43_real_jacobian_weight hz)
  have htop : ∫⁻ w in koebeDomain, g w ∂volume = ⊤ := by
    have hcongr : ∫⁻ z in disk,
        ENNReal.ofReal |(f' z).det| * g (koebeMap z) ∂volume =
      ∫⁻ z in disk, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (2 / 3 : ℝ)) ∂volume :=
      MeasureTheory.setLIntegral_congr_fun hs hweight
    change ∫⁻ w in koebeMap '' disk, g w ∂volume = ⊤
    rw [hcov, hcongr]
    simpa [areaMoment] using inv43_areaMoment_two_thirds_top
  intro hInt
  have hlt := hInt.setLIntegral_lt_top
  rw [htop] at hlt
  exact lt_irrefl _ hlt
theorem inv4_neg_two_uniform_bound {n : ℕ} {z : ℂ}
    (hz : z ∈ Metric.ball (((1 - ((1 : ℝ) / 2) ^ n : ℝ) : ℂ) * (-1 : ℂ))
      (((1 : ℝ) / 2) ^ n / 4)) :
    (3 / 4 : ℝ) ^ 6 * (5 * ((1 : ℝ) / 2) ^ n / 4) ^ (-2 : ℝ) ≤
      ‖deriv koebeMap z‖ ^ (-2 : ℝ) := by
  set r : ℝ := ((1 : ℝ) / 2) ^ n with hr
  have hrpos : 0 < r := pow_pos (by norm_num) n
  have hrle : r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hzdisk : z ∈ disk :=
    koebeModel_ball_subset_disk (a := (-1 : ℂ)) (by norm_num) n (by simpa [r] using hz)
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hzdisk
  have hz1 : z ≠ 1 := by
    intro h
    subst h
    norm_num at hznorm
  have hzneg1 : z ≠ -1 := by
    intro h
    subst h
    rw [norm_neg, norm_one] at hznorm
    norm_num at hznorm
  have hA_le : ‖1 + z‖ ≤ 5 * r / 4 := by
    have h := koebeModel_norm_sub_le (a := (-1 : ℂ)) (by norm_num) n (by simpa [r] using hz)
    simpa [r, add_comm] using h
  have hA_pos : 0 < ‖1 + z‖ := by
    apply norm_pos_iff.mpr
    intro h
    apply hzneg1
    linear_combination h
  have hB_ge : (3 / 4 : ℝ) ≤ ‖1 - z‖ := by
    have htri : ‖(2 : ℂ)‖ ≤ ‖1 - z‖ + ‖1 + z‖ := by
      calc ‖(2 : ℂ)‖ = ‖(1 - z) + (1 + z)‖ := by
            congr 1
            ring
        _ ≤ _ := norm_add_le _ _
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num] at htri
    linarith
  have hB_pos : 0 < ‖1 - z‖ := lt_of_lt_of_le (by norm_num) hB_ge
  have hA_sq_pos : 0 < ‖1 + z‖ ^ 2 := by positivity
  have hA_sq_le : ‖1 + z‖ ^ 2 ≤ (5 * r / 4) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hA_le 2
  have hB6 : (3 / 4 : ℝ) ^ 6 ≤ ‖1 - z‖ ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hB_ge 6
  have hchain : (3 / 4 : ℝ) ^ 6 / (5 * r / 4) ^ 2 ≤
      ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 := by
    calc (3 / 4 : ℝ) ^ 6 / (5 * r / 4) ^ 2
        ≤ ‖1 - z‖ ^ 6 / (5 * r / 4) ^ 2 :=
          div_le_div_of_nonneg_right hB6 (sq_nonneg _)
      _ ≤ ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 :=
          div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg _) 6) hA_sq_pos hA_sq_le
  have hneg : ‖deriv koebeMap z‖ ^ (-2 : ℝ) = ‖1 - z‖ ^ 6 / ‖1 + z‖ ^ 2 := by
    rw [schlicht_deriv_norm hz1]
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity), Real.rpow_two,
      div_pow]
    rw [inv_div]
    congr 1
    rw [show (‖1 - z‖ ^ 3) ^ 2 = ‖1 - z‖ ^ 6 by ring]
  rw [hneg]
  have hscale : (5 * r / 4) ^ (-2 : ℝ) = ((5 * r / 4) ^ 2)⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hscale, div_eq_mul_inv]
  exact hchain
theorem inv4_areaMoment_neg_two_top : areaMoment koebeMap disk (-2) = ⊤ := by
  have h := lintegral_eq_top_of_ball_ge (S := disk)
    (g := fun z => ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)))
    (a := (-1 : ℂ)) (by norm_num)
    (fun n => koebeModel_ball_subset_disk (a := (-1 : ℂ)) (by norm_num) n)
    (by fun_prop) (c := (3 / 4 : ℝ) ^ 6) (by positivity)
    (fun n z hz => ENNReal.ofReal_le_ofReal (inv4_neg_two_uniform_bound hz))
  simpa [areaMoment] using h
lemma inv4_jacobian_arith {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (A / B ^ 3) ^ 2 * (B ^ 12 / A ^ 4) = (A / B ^ 3) ^ (-2 : ℝ) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  field_simp [hA.ne', hB.ne']
lemma inv4_norm_deriv_koebeInverse_koebeMap {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeInverse (koebeMap z)‖ ^ (4 : ℝ) =
      ‖1 - z‖ ^ 12 / ‖1 + z‖ ^ 4 := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hznorm
  rw [deriv_inv43_koebeInverse_koebeMap hz]
  rw [norm_div, norm_pow]
  rw [show ((4 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]
  rw [show (‖1 - z‖ ^ 3) ^ 4 = ‖1 - z‖ ^ 12 by ring]
lemma inv4_abs_det_fderiv_koebeMap' {z : ℂ} (hz : z ≠ 1) :
    |(fderiv ℝ koebeMap z).det| = ‖deriv koebeMap z‖ ^ 2 :=
  inv43_abs_det_fderiv_koebeMap hz
lemma inv4_real_jacobian_weight {z : ℂ} (hz : z ∈ disk) :
    ‖deriv koebeMap z‖ ^ 2 *
        (‖1 - z‖ ^ 12 / ‖1 + z‖ ^ 4) =
      ‖deriv koebeMap z‖ ^ (-2 : ℝ) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hznorm
  have hB : 0 < ‖1 - z‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hz1.symm
  have hA : 0 < ‖1 + z‖ := by
    rw [norm_pos_iff]
    intro h
    have hz' : z = -1 := by linear_combination h
    subst hz'
    rw [norm_neg, norm_one] at hznorm
    norm_num at hznorm
  rw [schlicht_deriv_norm hz1]
  exact inv4_jacobian_arith hA hB
lemma inv4_jacobian_weight_mul {z : ℂ} (hz : z ∈ disk) :
    ENNReal.ofReal |(fderiv ℝ koebeMap z).det| *
        ENNReal.ofReal (‖deriv koebeInverse (koebeMap z)‖ ^ (4 : ℝ)) =
      ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) := by
  have hznorm : ‖z‖ < 1 := by
    simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hznorm
  rw [← ENNReal.ofReal_mul (abs_nonneg (fderiv ℝ koebeMap z).det)]
  rw [inv43_abs_det_fderiv_koebeMap hz1]
  rw [inv4_norm_deriv_koebeInverse_koebeMap hz]
  exact congrArg ENNReal.ofReal (inv4_real_jacobian_weight hz)
theorem inv_deriv_four_not_integrable :
    ¬ MeasureTheory.IntegrableOn
      (fun z => ‖deriv koebeInverse z‖ ^ (4 : ℝ)) koebeDomain volume := by
  let g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖deriv koebeInverse w‖ ^ (4 : ℝ))
  have hs : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  let f' : ℂ → ℂ →L[ℝ] ℂ := fun z => deriv koebeMap z • (1 : ℂ →L[ℝ] ℂ)
  have hf' : ∀ z ∈ disk, HasFDerivWithinAt koebeMap (f' z) disk z := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hznorm
    simpa [f', (schlicht_hasDerivAt_koebeMap hz1).deriv] using
      ((schlicht_hasDerivAt_koebeMap hz1).complexToReal_fderiv).hasFDerivWithinAt
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) (s := disk) (f := koebeMap) (f' := f') hs hf' koebe_schlicht.1.2 g
  have hweight : ∀ z ∈ disk,
      ENNReal.ofReal |(f' z).det| * g (koebeMap z) =
        ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) := by
    intro z hz
    have hznorm : ‖z‖ < 1 := by
      simpa [disk, Metric.mem_ball, dist_eq_norm] using hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hznorm
    dsimp [f', g]
    rw [inv43_det_real_complex_smul_one, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (sq_nonneg _), inv4_norm_deriv_koebeInverse_koebeMap hz,
      ← ENNReal.ofReal_mul (sq_nonneg ‖deriv koebeMap z‖)]
    exact congrArg ENNReal.ofReal (inv4_real_jacobian_weight hz)
  have htop : ∫⁻ w in koebeDomain, g w ∂volume = ⊤ := by
    have hcongr : ∫⁻ z in disk,
        ENNReal.ofReal |(f' z).det| * g (koebeMap z) ∂volume =
      ∫⁻ z in disk, ENNReal.ofReal (‖deriv koebeMap z‖ ^ (-2 : ℝ)) ∂volume :=
      MeasureTheory.setLIntegral_congr_fun hs hweight
    change ∫⁻ w in koebeMap '' disk, g w ∂volume = ⊤
    rw [hcov, hcongr]
    simpa [areaMoment] using inv4_areaMoment_neg_two_top
  intro hInt
  have hlt := hInt.setLIntegral_lt_top
  rw [htop] at hlt
  exact lt_irrefl _ hlt
theorem sharp_endpoints : SharpEndpointStatement :=
  ⟨koebe_schlicht, areaMoment_neg_two_top, areaMoment_two_thirds_top,
   inv_deriv_four_not_integrable, inv_deriv_four_thirds_not_integrable⟩
end Sharp
end Brennan

end

end OAI
