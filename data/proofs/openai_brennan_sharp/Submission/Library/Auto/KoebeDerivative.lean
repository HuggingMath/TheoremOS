import Mathlib

/-! # TheoremOS auto-library module `KoebeDerivative`

Records the derivative of the Koebe map w ↦ w/(1-w)^2, namely (1+z)/(1-z)^3 at any z ≠ 1, together with the resulting modulus formula ‖deriv‖ = ‖1+z‖/‖1-z‖^3. These are the standard calculus facts that convert powers of ‖deriv‖ of the Koebe map into the explicit weights ‖1+z‖^a/‖1-z‖^b used in divergence and integrability estimates.

Planned use for the triggering challenge:
* OAI.Brennan.Sharp.sharp_endpoints: Apply TheoremOS.Auto.KoebeDerivative.norm_deriv_koebeMap with z in the unit disk (so z ≠ 1, since 1 ∉ disk) after rewriting the challenge's `koebeMap z = z/(1-z)^2`; this yields ‖deriv koebeMap z‖ = ‖1+z‖/‖1-z‖^3. Raising to the real powers used in the sharp-endpoint computation then gives ‖deriv koebeMap z‖^(2/3) = ‖1+z‖^(2/3)/‖1-z‖^2 and ‖deriv koebeMap z‖^(-2) = ‖1-z‖^6/‖1+z‖^2, which are the pointwise weights compared against ‖z - 1‖^(-2) and ‖z + 1‖^(-2) near the boundary points 1 and -1. The HasDerivAt form supplies the differentiability input for any change-of-variables step.
* Remaining: Comparison of the explicit weights ‖1+z‖^(2/3)/‖1-z‖^2 and ‖1-z‖^6/‖1+z‖^2 with constant multiples of ‖z-1‖^(-2) and ‖z+1‖^(-2) on a neighbourhood inside the disk.
* Remaining: Divergence of the planar integral of ‖z - a‖^t over the unit disk when ‖a‖ = 1 and t ≤ -2 (the failed divergence lemma, still open).
* Remaining: Derivative formula for the inverse of the Koebe map on the Koebe domain and the change-of-variables transport of the two non-integrability statements.
* Remaining: Measurability and the Integrable-iff-lintegral conversion to obtain the two ¬ IntegrableOn conclusions.
* Remaining: Univalence of the Koebe map on the unit disk and the normalisation facts koebeMap 0 = 0, deriv koebeMap 0 = 1 needed for the Schlicht conjunct.

Sources:
* P. L. Duren, Univalent Functions, Springer, 1983 (the Koebe function k(z) = z/(1-z)^2 and its derivative).
* Standard complex calculus: quotient rule, chain rule, ‖w^n‖ = ‖w‖^n and ‖w/v‖ = ‖w‖/‖v‖.

Written by the TheoremOS library planner and proved by a TheoremOS solver run before solving the problem
recorded in the pool record. Only declarations Lean accepted with no gaps are kept. -/

/-!
# The derivative of the Koebe map `z ↦ z / (1 - z)^2`

The Koebe map is the basic example of a schlicht function on the unit disk.  Its
derivative is elementary but is the input to every estimate on the growth of
`‖deriv‖`; the two lemmas below record the value and its modulus in the form in
which power estimates are applied.

`HasDerivAt` is stated for the explicit function so that a caller whose own
definition is syntactically equal to `fun w => w / (1 - w) ^ 2` can rewrite.
-/

namespace TheoremOS.Auto.KoebeDerivative

open Complex

/-- Derivative of the Koebe map: away from the pole `z = 1`,
`d/dz (z / (1 - z)^2) = (1 + z) / (1 - z)^3`. -/
theorem hasDerivAt_koebeMap {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt (fun w : ℂ => w / (1 - w) ^ 2) ((1 + z) / (1 - z) ^ 3) z := by
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

/-- The modulus of the derivative of the Koebe map:
`‖d/dz (z / (1 - z)^2)‖ = ‖1 + z‖ / ‖1 - z‖ ^ 3` for `z ≠ 1`. -/
theorem norm_deriv_koebeMap {z : ℂ} (hz : z ≠ 1) :
    ‖deriv (fun w : ℂ => w / (1 - w) ^ 2) z‖ = ‖1 + z‖ / ‖1 - z‖ ^ 3 := by
  rw [(hasDerivAt_koebeMap hz).deriv, norm_div, norm_pow]

end TheoremOS.Auto.KoebeDerivative
