import Mathlib

/-! # TheoremOS auto-library module `ThreeStateChannelSpectrum`

Defines the transition matrix of the symmetric three-state channel, P(lam)(i,j) = (1+2lam)/3 for i=j and (1-lam)/3 otherwise, and proves its eigenvector action: P(lam) *ᵥ x = ((1-lam)/3 * sum_i x_i) • 1 + lam • x, together with the n-step version (P(lam)^n) *ᵥ x = ((1-lam^n)/3 * sum_i x_i) • 1 + lam^n • x. Taking x to be a difference of unit vectors and the uniform vector gives P(lam)^n(i,j) - 1/3 = lam^n (delta_ij - 1/3), so correlations decay exactly like lam^n. This is the standard eigenvalue computation underlying the Kesten-Stigum reconstruction threshold.

Planned use for the triggering challenge:
* OAI.ThreeState.regular_supercritical: Use TheoremOS.Auto.ThreeStateChannelSpectrum.channelMatrix_pow_mulVec. The challenge's channel is exactly channelMatrix lam (it is defined by the same if i=j then (1+2*lam)/3 else (1-lam)/3). Apply the power identity to the vector x = e_a - u, where e_a is a unit vector at root state a and u is the constant vector 1/3; its coordinate sum is 1 - 3*(1/3) = 0, so the first summand vanishes and (channelMatrix lam ^ n) *ᵥ x = lam^n • x. Reading coordinates gives P^n(a,j) - 1/3 = lam^n (delta_{a j} - 1/3): the n-step transition probabilities approach uniform at rate lam^n. This supplies the correlation decay needed to compare the root-a law with the uniform mixture, since after n generations the signal-to-noise ratio scales like b^n * lam^{2n} = (b * lam^2)^n, and the hypothesis hcrit : 1 < b * lam^2 makes this grow. All premises of the lemma (a real lam, a natural n, an arbitrary real vector on Fin 3) are immediate; the only input used is the definition of channelMatrix, which unfolds to the challenge's channel. The Poisson case is identical with b replaced by d.
* Remaining: Relate the real channel matrix to the PMF channelPMF: show the entries of channelPMF are ENNReal.ofReal of channelMatrix entries and that (channelPMF lam h i j).toReal = channelMatrix lam i j.
* Remaining: Iterate the broadcast to obtain the n-step law of a single leaf given the root: the leaf-state marginal is the n-th convolution power of the channel, so the power identity yields its deviation lambda^n (delta_ij - 1/3) from uniform.
* Remaining: Expand the tree: the offspring law needs its first and second moments; for regular b the observed law at depth n is a b^n-fold independent sample, and for Poisson d the offspring moments come from the exponential generating function of poissonOffspring.
* Remaining: Control the effect of the root on the marginal by a chi-square/second-moment computation, then convert the resulting squared-distance (Hellinger/chi-square) estimate into the total-variation quantities appearing in advantage.
* Remaining: Use the existing TheoremOS.Probability.TreeReconstruction library for pmfTV and reconAdvantage, and prove the bridge identity that the challenge's advantage (sum over observations of marginal times half the sum of posterior deviations) equals (1/3) times the sum over the three root states of pmfTV of law i from the uniform mixture.
* Remaining: Handle the degenerate observations where the marginal mass is zero, using the if-then-else convention in posterior without changing the value of advantage.
* Remaining: Prove monotonicity/convergence of the resulting scalar recursion when 1 < b * lam^2 (regular case) and 1 < d * lam^2 (Poisson case), obtaining Filter.Tendsto ... atTop (nhds L) for the two advantage sequences.
* Remaining: Assemble the two headline theorems regular_supercritical and poisson_supercritical from the above, using Admissible to ensure channel_nonneg so that channelPMF is a genuine PMF.

Sources:
* H. Kesten and B. P. Stigum, Additional limit theorems for indecomposable multidimensional Galton-Watson processes, Ann. Math. Statist. 37 (1966).
* E. Mossel, Survey: Information flow on trees, in Graphs, Morphisms and Statistical Physics, DIMACS Ser. Discrete Math. Theoret. Comput. Sci. 63 (2004).
* C. Borgs, J. Chayes, L. Lovasz and K. Vesztergombi, Counting graph homomorphisms, in Topics in Discrete Mathematics (2006), for the symmetric-channel spectral decomposition.

Written by the TheoremOS library planner and proved by a TheoremOS solver run before solving the problem
recorded in the pool record. Only declarations Lean accepted with no gaps are kept. -/

/-!
# The spectrum of the three-state symmetric channel

The channel matrix `P(lam)` with entries `(1 + 2*lam)/3` on the diagonal and
`(1 - lam)/3` off the diagonal is `((1 - lam)/3) smul J + lam smul 1`, where `J`
is the all-ones matrix.  Consequently its action on a vector `x` splits off the
component along the constant vector:
`P(lam) *ᵥ x = ((1 - lam)/3 * sum i, x i) smul 1 + lam smul x`.
Iterating gives
`(P(lam)^n) *ᵥ x = ((1 - lam^n)/3 * sum i, x i) smul 1 + lam^n smul x`,
so the deviation of the `n`-step transition probabilities from the uniform
distribution decays like `lam^n`.  This is the eigenvalue computation behind the
Kesten-Stigum threshold for reconstruction on trees.
-/

open Matrix
open scoped BigOperators

namespace TheoremOS.Auto.ThreeStateChannelSpectrum

/-- The transition matrix of the symmetric three-state channel with parameter `lam`. -/
noncomputable def channelMatrix (lam : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

/-- The channel acts on a vector by keeping a `lam` fraction of its deviation from the
constant vector and replacing its mean by the same mean. -/
theorem channelMatrix_mulVec_eq (lam : ℝ) (x : Fin 3 → ℝ) :
    channelMatrix lam *ᵥ x
      = ((1 - lam) / 3 * ∑ i, x i) • (fun _ => (1 : ℝ)) + lam • x := by
  ext i
  fin_cases i <;>
    simp [channelMatrix, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three] <;> ring

/-- The `n`-step transition matrix keeps only a `lam^n` fraction of the deviation
from the uniform vector. -/
theorem channelMatrix_pow_mulVec (lam : ℝ) (n : ℕ) (x : Fin 3 → ℝ) :
    (channelMatrix lam ^ n) *ᵥ x
      = ((1 - lam ^ n) / 3 * ∑ i, x i) • (fun _ => (1 : ℝ)) + lam ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, channelMatrix_mulVec_eq]
      ext i
      fin_cases i <;>
        simp [Fin.sum_univ_three, pow_succ] <;> ring

end TheoremOS.Auto.ThreeStateChannelSpectrum
