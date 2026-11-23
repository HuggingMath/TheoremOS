import ArchivedHopfRinowHelpers
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set
open scoped ContDiff

namespace TheoremOS.WeakFundamentalTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The test-function identity for a weak derivative on an open set. -/
def HasWeakDerivativeOn (f g : ℝ → E) (U : Set ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ t : ℝ, deriv φ t • f t) = -(∫ t : ℝ, φ t • g t)

/-- A locally integrable function with a continuous weak derivative agrees almost everywhere
with a primitive plus a constant. -/
theorem ae_eq_add_intervalIntegral {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : LocallyIntegrableOn f (Ioo a b)) (hg : Continuous g)
    (hweak : HasWeakDerivativeOn f g (Ioo a b)) :
    ∃ c : E, f =ᵐ[volume.restrict (Ioo a b)] (fun x => c + ∫ t in a..x, g t) := by
  let G : ℝ → E := fun x => ∫ t in a..x, g t
  have hG (x : ℝ) : HasDerivAt G (g x) x :=
    (hg.integral_hasStrictDerivAt a x).hasDerivAt
  have hGcont : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  have hGloc : LocallyIntegrableOn G (Ioo a b) :=
    hGcont.continuousOn.locallyIntegrableOn measurableSet_Ioo
  -- Subtract the classical primitive and use the archived vanishing-derivative lemma.
  obtain ⟨c, hc⟩ := Submission.Helpers.ae_eq_const_of_test_deriv_integral_zero a b hab
    (fun t => f t - G t) (hf.sub hGloc) (by
      intro φ hφ hcφ hsφ
      have hφ' := hφ.continuous_deriv (by simp)
      have hfφ := Submission.Helpers.integrable_test_smul_of_locallyIntegrableOn hf
        (deriv φ) hφ' hcφ.deriv (tsupport_deriv_subset.trans hsφ)
      have hGφ : Integrable (fun t => deriv φ t • G t) :=
        (hφ'.smul hGcont).integrable_of_hasCompactSupport hcφ.deriv.smul_right
      have hweakG : (∫ t : ℝ, φ t • g t) = -(∫ t : ℝ, deriv φ t • G t) :=
        integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
          (L := ContinuousLinearMap.lsmul ℝ ℝ)
          (fun x _ => (hφ.differentiable (by simp) x).hasDerivAt)
          (fun x _ => hG x)
          ((hφ.continuous.smul hg).integrable_of_hasCompactSupport hcφ.smul_right)
          hGφ ((hφ.continuous.smul hGcont).integrable_of_hasCompactSupport hcφ.smul_right)
      simp_rw [smul_sub]
      rw [integral_sub hfφ hGφ, hweak φ hφ hcφ hsφ, hweakG, neg_neg, sub_self])
  refine ⟨c, (ae_restrict_iff' measurableSet_Ioo).mpr ?_⟩
  filter_upwards [hc] with x hx hxab
  exact sub_eq_iff_eq_add.mp (hx hxab)

/-- For continuous representatives the weak derivative recovers every increment on the interval. -/
theorem sub_eq_intervalIntegral {a b : ℝ} (hab : a < b) {f g : ℝ → E}
    (hf : ContinuousOn f (Ioo a b)) (hg : Continuous g)
    (hweak : HasWeakDerivativeOn f g (Ioo a b)) {x y : ℝ}
    (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    f y - f x = ∫ t in x..y, g t := by
  obtain ⟨c, hc⟩ := ae_eq_add_intervalIntegral hab (hf.locallyIntegrableOn measurableSet_Ioo) hg hweak
  have hG : Continuous (fun z => c + ∫ t in a..z, g t) :=
    continuous_const.add (continuous_iff_continuousAt.mpr
      fun z => (hg.integral_hasStrictDerivAt a z).hasDerivAt.continuousAt)
  have h := Measure.eqOn_open_of_ae_eq hc isOpen_Ioo hf hG.continuousOn
  rw [h hy, h hx]
  dsimp only
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable a x) (hg.intervalIntegrable x y)]
  abel

#print axioms ae_eq_add_intervalIntegral
#print axioms sub_eq_intervalIntegral

end TheoremOS.WeakFundamentalTheorem
