import Submission.Library.TheoremOS.InformationTheory.Entropy

/-!
# Finite probability and total variation distance

Weights `p : Ω → ℝ` on a finite type, with `IsDistribution p` (nonnegative, sum one) from
`TheoremOS.InformationTheory.Entropy`. Contents: expectation `expectation p X = ∑ ω, p ω * X ω`
and event probability `prob p s = ∑ ω ∈ s, p ω`; linearity and monotonicity, the union bound,
complements, Markov's and Chebyshev's inequalities, variance `E X² - (E X)²`, and the second
moment bound `(E X)² ≤ P(X ≠ 0) · E X²`. Total variation `tvDist p q = ½ ∑ |p - q|`: a
pseudometric, at most one between distributions, the maximal event gap, contraction under
pushforwards and under row-stochastic kernels (`Matrix.rowStochastic`), the coupling bound,
the `√|Ω|` comparison with the `ℓ²` distance, and subadditivity on products. Markov chains:
a row-stochastic matrix maps distributions to distributions, detailed balance gives a
stationary vector, averages `n⁻¹ ∑ i, K i` of kernels are kernels with the common stationary
vectors, the heat-bath (Glauber) kernel of an equivalence relation is a kernel reversible for
its weights, and the distance to a stationary distribution (from a start vector, a start state,
or the worst start state) is nonincreasing.

Sources: D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS, 2017,
§1.6 (detailed balance), §3.3 (Glauber dynamics), §4.1–4.2 (total variation, couplings), §4.4 (the distance `d(t)` is
nonincreasing); N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016,
Chapter 4 (Markov, Chebyshev, second moment). Textbook material; nothing here is specific to a
benchmark problem.

Bridges: a statement defining total variation as `(1 / 2 : ℝ) * ∑ y, |p y - q y|` is
`tvDist p q` by `rfl`; the forms `(1 / ((2 : ℕ) : ℝ)) * ∑ …` and `(∑ …) / 2` are
`tvDist_eq_natCast_half` and `tvDist_eq_sum_div_two`; a sum over `Finset.univ` written through a
definition such as `allGraphStates` unfolds to `∑ y` first; the constant `1 / N` with
`N = Fintype.card Ω` is `InformationTheory.uniform Ω` by `uniform_eq_one_div`. The row
`(P ^ (t + 1)) x` is `(P ^ t) x ᵥ* P` by `pow_succ_row`, and a start vector `μ` evolves as
`μ ᵥ* P ^ t`. A site kernel `if sameExcept i x y then w y / ∑ z, (if sameExcept i x z then w z
else 0) else 0` is `heatBath (sameExcept i) w` by `rfl`, and `(n : ℝ)⁻¹ • ∑ i, K i` is covered by
`inv_natCast_smul_sum_mem_rowStochastic` and `vecMul_inv_natCast_smul_sum`. Short names such
as `expectation`, `variance` and `heatBath` also occur in problem namespaces; write
`TheoremOS.Probability.variance` etc. when both are in scope.
-/

namespace TheoremOS.Probability

open Finset Matrix
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

/-- Expectation of `X` under the weights `p`. -/
def expectation (p : Ω → ℝ) (X : Ω → ℝ) : ℝ := ∑ ω, p ω * X ω

/-- Mass of the event `s` under the weights `p`. -/
def prob (p : Ω → ℝ) (s : Finset Ω) : ℝ := ∑ ω ∈ s, p ω

section Expectation

lemma expectation_add (p X Y : Ω → ℝ) :
    expectation p (X + Y) = expectation p X + expectation p Y := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p X Y : Ω → ℝ) :
    expectation p (X - Y) = expectation p X - expectation p Y := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_const_mul (p X : Ω → ℝ) (c : ℝ) :
    expectation p (fun ω => c * X ω) = c * expectation p X := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

lemma expectation_const {p : Ω → ℝ} (hp : IsDistribution p) (c : ℝ) :
    expectation p (fun _ => c) = c := by
  simp only [expectation, ← Finset.sum_mul, hp.sum_eq_one, one_mul]

lemma expectation_mono {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    expectation p X ≤ expectation p Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hp ω)

lemma expectation_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) :
    0 ≤ expectation p X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω) (hX ω)

lemma prob_eq_expectation_indicator (p : Ω → ℝ) (s : Finset Ω) [DecidablePred (· ∈ s)] :
    prob p s = expectation p (fun ω => if ω ∈ s then 1 else 0) := by
  simp [prob, expectation]

omit [Fintype Ω] in
lemma prob_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (s : Finset Ω) : 0 ≤ prob p s :=
  Finset.sum_nonneg fun ω _ => hp ω

omit [Fintype Ω] in
lemma prob_mono {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {s t : Finset Ω} (hst : s ⊆ t) :
    prob p s ≤ prob p t :=
  Finset.sum_le_sum_of_subset_of_nonneg hst fun ω _ _ => hp ω

lemma prob_univ {p : Ω → ℝ} (hp : IsDistribution p) : prob p Finset.univ = 1 :=
  hp.sum_eq_one

lemma prob_le_one {p : Ω → ℝ} (hp : IsDistribution p) (s : Finset Ω) : prob p s ≤ 1 :=
  (prob_mono hp.nonneg (Finset.subset_univ s)).trans_eq (prob_univ hp)

lemma prob_compl [DecidableEq Ω] {p : Ω → ℝ} (hp : IsDistribution p) (s : Finset Ω) :
    prob p sᶜ = 1 - prob p s := by
  have h := Finset.sum_compl_add_sum s p
  rw [hp.sum_eq_one] at h
  simp only [prob]
  linarith

omit [Fintype Ω] in
/-- The union bound for two events. -/
lemma prob_union_le [DecidableEq Ω] {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (s t : Finset Ω) :
    prob p (s ∪ t) ≤ prob p s + prob p t := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := p)
  have h0 : 0 ≤ ∑ ω ∈ s ∩ t, p ω := Finset.sum_nonneg fun ω _ => hp ω
  simp only [prob]
  linarith
omit [Fintype Ω] in
/-- The union bound for a finite family of events. -/
lemma prob_biUnion_le [DecidableEq Ω] {ι : Type*} {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω)
    (I : Finset ι) (s : ι → Finset Ω) :
    prob p (I.biUnion s) ≤ ∑ i ∈ I, prob p (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [prob]
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (prob_union_le hp _ _).trans (by linarith)

/-- **Markov's inequality**. -/
theorem markov {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {a : ℝ}
    (ha : 0 < a) : prob p {ω | a ≤ X ω} ≤ expectation p X / a := by
  rw [le_div_iff₀ ha]
  calc prob p {ω | a ≤ X ω} * a = ∑ ω ∈ {ω | a ≤ X ω}, p ω * a := by
        rw [prob, Finset.sum_mul]
    _ ≤ ∑ ω ∈ {ω | a ≤ X ω}, p ω * X ω := by
        refine Finset.sum_le_sum fun ω hω => ?_
        exact mul_le_mul_of_nonneg_left (Finset.mem_filter.1 hω).2 (hp ω)
    _ ≤ expectation p X :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun ω _ _ => mul_nonneg (hp ω) (hX ω)

/-- Variance `E (X - E X)²`. -/
def variance (p : Ω → ℝ) (X : Ω → ℝ) : ℝ :=
  expectation p (fun ω => (X ω - expectation p X) ^ 2)

lemma variance_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) : 0 ≤ variance p X :=
  expectation_nonneg hp fun _ => sq_nonneg _

lemma expectation_sub_const_sq {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → ℝ) (m : ℝ) :
    expectation p (fun ω => (X ω - m) ^ 2) =
      expectation p (fun ω => X ω ^ 2) - 2 * m * expectation p X + m ^ 2 := by
  have h : ∀ ω, p ω * (X ω - m) ^ 2 = p ω * X ω ^ 2 - 2 * m * (p ω * X ω) + m ^ 2 * p ω :=
    fun ω => by ring
  simp only [expectation, h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hp.sum_eq_one, mul_one]

/-- `Var X = E X² - (E X)²`. -/
theorem variance_eq {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → ℝ) :
    variance p X = expectation p (fun ω => X ω ^ 2) - expectation p X ^ 2 := by
  rw [variance, expectation_sub_const_sq hp]
  ring

lemma sq_expectation_le {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → ℝ) :
    expectation p X ^ 2 ≤ expectation p (fun ω => X ω ^ 2) := by
  have := variance_nonneg hp.nonneg X
  rw [variance_eq hp] at this
  linarith

/-- **Chebyshev's inequality**. -/
theorem chebyshev {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → ℝ) {a : ℝ} (ha : 0 < a) :
    prob p {ω | a ≤ |X ω - expectation p X|} ≤ variance p X / a ^ 2 := by
  have hset : ({ω | a ≤ |X ω - expectation p X|} : Finset Ω) =
      ({ω | a ^ 2 ≤ (X ω - expectation p X) ^ 2} : Finset Ω) :=
    Finset.filter_congr fun ω _ => by
      rw [← sq_abs (X ω - expectation p X)]
      exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) two_ne_zero).symm
  rw [hset]
  exact markov hp.nonneg (fun _ => sq_nonneg _) (pow_pos ha 2)
/-- The **second moment bound** `(E X)² ≤ P(X ≠ 0) · E X²` (Cauchy–Schwarz on the support). -/
theorem sq_expectation_le_prob_ne_zero_mul {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) :
    expectation p X ^ 2 ≤ prob p {ω | X ω ≠ 0} * expectation p (fun ω => X ω ^ 2) := by
  have h1 : ∀ ω, √(p ω) ^ 2 = p ω := fun ω => Real.sq_sqrt (hp ω)
  have hE : expectation p X = ∑ ω ∈ {ω | X ω ≠ 0}, √(p ω) * (√(p ω) * X ω) := by
    have h : ∀ ω, √(p ω) * (√(p ω) * X ω) = p ω * X ω := fun ω => by
      rw [← mul_assoc, Real.mul_self_sqrt (hp ω)]
    simp only [h]
    rw [expectation, Finset.sum_filter_of_ne]
    intro ω _ hω
    exact right_ne_zero_of_mul hω
  rw [hE]
  calc (∑ ω ∈ {ω | X ω ≠ 0}, √(p ω) * (√(p ω) * X ω)) ^ 2
      ≤ (∑ ω ∈ {ω | X ω ≠ 0}, √(p ω) ^ 2) * ∑ ω ∈ {ω | X ω ≠ 0}, (√(p ω) * X ω) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ prob p {ω | X ω ≠ 0} * expectation p (fun ω => X ω ^ 2) := by
        have h2 : ∀ ω, (√(p ω) * X ω) ^ 2 = p ω * X ω ^ 2 := fun ω => by rw [mul_pow, h1]
        simp only [h1, h2]
        refine mul_le_mul_of_nonneg_left ?_ (prob_nonneg hp _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun ω _ _ => mul_nonneg (hp ω) (sq_nonneg _)

/-- The **second moment method**: `P(X ≠ 0) ≥ (E X)² / E X²`. -/
theorem sq_expectation_div_le_prob_ne_zero {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) :
    expectation p X ^ 2 / expectation p (fun ω => X ω ^ 2) ≤ prob p {ω | X ω ≠ 0} := by
  rcases (expectation_nonneg hp fun ω => sq_nonneg (X ω)).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact prob_nonneg hp _
  · rw [div_le_iff₀ h]
    exact sq_expectation_le_prob_ne_zero_mul hp X

end Expectation

section TotalVariation

/-- Total variation distance `½ ∑ |p - q|`. -/
def tvDist (p q : Ω → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ ω, |p ω - q ω|

lemma tvDist_eq_natCast_half (p q : Ω → ℝ) :
    (1 / ((2 : ℕ) : ℝ)) * ∑ ω, |p ω - q ω| = tvDist p q := by
  norm_num [tvDist]

lemma tvDist_eq_sum_div_two (p q : Ω → ℝ) : (∑ ω, |p ω - q ω|) / 2 = tvDist p q := by
  rw [tvDist]
  ring

lemma tvDist_comm (p q : Ω → ℝ) : tvDist p q = tvDist q p := by
  simp only [tvDist, abs_sub_comm]

@[simp] lemma tvDist_self (p : Ω → ℝ) : tvDist p p = 0 := by
  simp [tvDist]

lemma tvDist_nonneg (p q : Ω → ℝ) : 0 ≤ tvDist p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun ω _ => abs_nonneg _)

lemma tvDist_triangle (p q r : Ω → ℝ) : tvDist p r ≤ tvDist p q + tvDist q r := by
  simp only [tvDist, ← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => ?_) (by norm_num)
  exact abs_sub_le (p ω) (q ω) (r ω)

lemma tvDist_eq_zero_iff (p q : Ω → ℝ) : tvDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    have h' : ∑ ω, |p ω - q ω| = 0 := by
      simpa [tvDist] using h
    rw [Finset.sum_eq_zero_iff_of_nonneg fun ω _ => abs_nonneg _] at h'
    funext ω
    exact sub_eq_zero.1 (abs_eq_zero.1 (h' ω (Finset.mem_univ ω)))
  · rintro rfl
    exact tvDist_self p
/-- For weights of equal total mass, `tvDist p q = ∑ (p - q)⁺`. -/
lemma tvDist_eq_sum_max {p q : Ω → ℝ} (h : ∑ ω, p ω = ∑ ω, q ω) :
    tvDist p q = ∑ ω, max (p ω - q ω) 0 := by
  have h0 : ∑ ω, (p ω - q ω) = 0 := by rw [Finset.sum_sub_distrib, h, sub_self]
  have habs : ∀ x : ℝ, |x| = 2 * max x 0 - x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx]; ring
    · rw [abs_of_nonpos hx, max_eq_right hx]; ring
  simp only [tvDist, habs, Finset.sum_sub_distrib, h0, ← Finset.mul_sum]
  ring

/-- Every event gap is at most the total variation distance. -/
theorem prob_sub_prob_le_tvDist {p q : Ω → ℝ} (h : ∑ ω, p ω = ∑ ω, q ω) (s : Finset Ω) :
    prob p s - prob q s ≤ tvDist p q := by
  rw [tvDist_eq_sum_max h, prob, prob, ← Finset.sum_sub_distrib]
  calc ∑ ω ∈ s, (p ω - q ω) ≤ ∑ ω ∈ s, max (p ω - q ω) 0 :=
        Finset.sum_le_sum fun ω _ => le_max_left _ _
    _ ≤ ∑ ω, max (p ω - q ω) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          fun ω _ _ => le_max_right _ _

theorem abs_prob_sub_prob_le_tvDist {p q : Ω → ℝ} (h : ∑ ω, p ω = ∑ ω, q ω) (s : Finset Ω) :
    |prob p s - prob q s| ≤ tvDist p q := by
  rw [abs_le]
  constructor
  · have := prob_sub_prob_le_tvDist h.symm s
    rw [tvDist_comm] at this
    linarith
  · exact prob_sub_prob_le_tvDist h s

/-- The event `{q < p}` attains the total variation distance. -/
theorem prob_sub_prob_lt_eq_tvDist {p q : Ω → ℝ} (h : ∑ ω, p ω = ∑ ω, q ω) :
    prob p {ω | q ω < p ω} - prob q {ω | q ω < p ω} = tvDist p q := by
  rw [tvDist_eq_sum_max h, prob, prob, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  split_ifs with hω
  · exact (max_eq_left (sub_nonneg.2 hω.le)).symm
  · exact (max_eq_right (sub_nonpos.2 (not_lt.1 hω))).symm

/-- Total variation is the largest event gap. -/
theorem isGreatest_tvDist {p q : Ω → ℝ} (h : ∑ ω, p ω = ∑ ω, q ω) :
    IsGreatest (Set.range fun s : Finset Ω => prob p s - prob q s) (tvDist p q) :=
  ⟨⟨_, prob_sub_prob_lt_eq_tvDist h⟩, by
    rintro _ ⟨s, rfl⟩
    exact prob_sub_prob_le_tvDist h s⟩

lemma tvDist_le_one {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    tvDist p q ≤ 1 := by
  rw [← prob_sub_prob_lt_eq_tvDist (hp.sum_eq_one.trans hq.sum_eq_one.symm)]
  have h1 := prob_le_one hp {ω | q ω < p ω}
  have h2 := prob_nonneg hq.nonneg {ω | q ω < p ω}
  linarith

/-- Total variation does not increase under a pushforward. -/
theorem tvDist_pushforward_le [DecidableEq Ω'] (f : Ω → Ω') (p q : Ω → ℝ) :
    tvDist (pushforward f p) (pushforward f q) ≤ tvDist p q := by
  simp only [tvDist]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ y, |pushforward f p y - pushforward f q y|
      = ∑ y, |∑ ω with f ω = y, (p ω - q ω)| := by
        simp only [pushforward, Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ ω with f ω = y, |p ω - q ω| :=
        Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, |p ω - q ω| := Finset.sum_fiberwise Finset.univ f _
/-- Total variation does not increase under a row-stochastic kernel. -/
theorem tvDist_vecMul_le [DecidableEq Ω] {P : Matrix Ω Ω ℝ} (hP : P ∈ rowStochastic ℝ Ω)
    (p q : Ω → ℝ) : tvDist (p ᵥ* P) (q ᵥ* P) ≤ tvDist p q := by
  simp only [tvDist]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ∑ y, |(p ᵥ* P) y - (q ᵥ* P) y| = ∑ y, |∑ x, (p x - q x) * P x y| := by
        simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ y, ∑ x, |(p x - q x) * P x y| :=
        Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |p x - q x| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [abs_mul, abs_of_nonneg (nonneg_of_mem_rowStochastic hP), ← Finset.mul_sum,
          sum_row_of_mem_rowStochastic hP, mul_one]

/-- The **coupling inequality**: `tvDist p q ≤ P(X ≠ Y)` for any coupling `(X, Y)`. -/
theorem tvDist_marginal_le [DecidableEq Ω] {r : Ω × Ω → ℝ} (hr : ∀ x, 0 ≤ r x) :
    tvDist (marginalLeft r) (marginalRight r) ≤ ∑ x with x.1 ≠ x.2, r x := by
  have hdiff : ∀ a, marginalLeft r a - marginalRight r a =
      ∑ b, ((if a ≠ b then r (a, b) else 0) - if b ≠ a then r (b, a) else 0) := by
    intro a
    simp only [marginalLeft, marginalRight, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hS : ∑ x with x.1 ≠ x.2, r x = ∑ a, ∑ b, if a ≠ b then r (a, b) else 0 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  have hswap : ∑ a, ∑ b, (if b ≠ a then r (b, a) else 0) =
      ∑ a, ∑ b, if a ≠ b then r (a, b) else 0 := Finset.sum_comm
  have hnn : ∀ a b, 0 ≤ if a ≠ b then r (a, b) else 0 := fun a b => by
    split_ifs
    · exact hr _
    · exact le_rfl
  calc tvDist (marginalLeft r) (marginalRight r)
      = (1 / 2 : ℝ) * ∑ a, |∑ b, ((if a ≠ b then r (a, b) else 0) -
          if b ≠ a then r (b, a) else 0)| := by
        simp only [tvDist, hdiff]
    _ ≤ (1 / 2 : ℝ) * ∑ a, ∑ b, ((if a ≠ b then r (a, b) else 0) +
          if b ≠ a then r (b, a) else 0) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by norm_num)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [abs_le]
        constructor <;> linarith [hnn a b, hnn b a]
    _ = ∑ x with x.1 ≠ x.2, r x := by
        rw [hS]
        simp only [Finset.sum_add_distrib, hswap]
        ring

/-- `tvDist p q ≤ ½ √|Ω| ‖p - q‖₂`. -/
theorem tvDist_le_sqrt_card_mul (p q : Ω → ℝ) :
    tvDist p q ≤ (1 / 2 : ℝ) * √(Fintype.card Ω) * √(∑ ω, (p ω - q ω) ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) fun ω => |p ω - q ω|
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sq_abs] at h
  rw [tvDist, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- Total variation is subadditive on products. -/
theorem tvDist_prod_le {p q : Ω → ℝ} {p' q' : Ω' → ℝ} (hq : IsDistribution q)
    (hp' : IsDistribution p') :
    tvDist (fun x : Ω × Ω' => p x.1 * p' x.2) (fun x => q x.1 * q' x.2) ≤
      tvDist p q + tvDist p' q' := by
  have key : ∀ x : Ω × Ω', |p x.1 * p' x.2 - q x.1 * q' x.2| ≤
      |p x.1 - q x.1| * p' x.2 + q x.1 * |p' x.2 - q' x.2| := fun x => by
    calc |p x.1 * p' x.2 - q x.1 * q' x.2|
        = |(p x.1 - q x.1) * p' x.2 + q x.1 * (p' x.2 - q' x.2)| := by congr 1; ring
      _ ≤ |(p x.1 - q x.1) * p' x.2| + |q x.1 * (p' x.2 - q' x.2)| := abs_add_le _ _
      _ = |p x.1 - q x.1| * p' x.2 + q x.1 * |p' x.2 - q' x.2| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hp'.nonneg _), abs_of_nonneg (hq.nonneg _)]
  calc tvDist (fun x : Ω × Ω' => p x.1 * p' x.2) (fun x => q x.1 * q' x.2)
      ≤ (1 / 2 : ℝ) * ∑ x : Ω × Ω', (|p x.1 - q x.1| * p' x.2 + q x.1 * |p' x.2 - q' x.2|) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => key x) (by norm_num)
    _ = tvDist p q + tvDist p' q' := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hp'.sum_eq_one,
          hq.sum_eq_one, mul_one, one_mul, tvDist]
        ring

lemma uniform_eq_one_div : uniform Ω = fun _ => 1 / (Fintype.card Ω : ℝ) := by
  funext ω
  simp [uniform]

end TotalVariation
section MarkovChain

variable [DecidableEq Ω] {P : Matrix Ω Ω ℝ}

/-- A row-stochastic kernel maps distributions to distributions. -/
lemma isDistribution_vecMul (hP : P ∈ rowStochastic ℝ Ω) {p : Ω → ℝ} (hp : IsDistribution p) :
    IsDistribution (p ᵥ* P) where
  nonneg y := Finset.sum_nonneg fun x _ => mul_nonneg (hp.nonneg x) (nonneg_of_mem_rowStochastic hP)
  sum_eq_one := by
    simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_row_of_mem_rowStochastic hP, mul_one, hp.sum_eq_one]

/-- Each row of a row-stochastic matrix is a distribution. -/
lemma isDistribution_row (hP : P ∈ rowStochastic ℝ Ω) (x : Ω) : IsDistribution (P x) :=
  ⟨fun _ => nonneg_of_mem_rowStochastic hP, sum_row_of_mem_rowStochastic hP x⟩

lemma pow_succ_row (P : Matrix Ω Ω ℝ) (t : ℕ) (x : Ω) : (P ^ (t + 1)) x = (P ^ t) x ᵥ* P := by
  funext y
  rw [_root_.pow_succ, Matrix.mul_apply]
  rfl

omit [DecidableEq Ω] in
/-- **Detailed balance** implies stationarity. -/
theorem vecMul_eq_of_detailedBalance {ν : Ω → ℝ} (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, ν x * P x y = ν y * P y x) : ν ᵥ* P = ν := by
  funext y
  calc (ν ᵥ* P) y = ∑ x, ν x * P x y := rfl
    _ = ∑ x, ν y * P y x := Finset.sum_congr rfl fun x _ => hrev x y
    _ = ν y := by rw [← Finset.mul_sum, hrow y, mul_one]

/-- An average of row-stochastic kernels is row stochastic. -/
lemma inv_card_smul_sum_mem_rowStochastic {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : ι → Matrix Ω Ω ℝ} (hK : ∀ i, K i ∈ rowStochastic ℝ Ω) :
    (Fintype.card ι : ℝ)⁻¹ • ∑ i, K i ∈ rowStochastic ℝ Ω := by
  rw [mem_rowStochastic_iff_sum]
  constructor
  · intro x y
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => nonneg_of_mem_rowStochastic (hK i))
  · intro x
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [sum_row_of_mem_rowStochastic (hK _), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The distance from a stationary `ν` is nonincreasing along the chain. -/
theorem tvDist_vecMul_pow_succ_le (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ} (hν : ν ᵥ* P = ν)
    (μ : Ω → ℝ) (t : ℕ) : tvDist (μ ᵥ* P ^ (t + 1)) ν ≤ tvDist (μ ᵥ* P ^ t) ν :=
  calc tvDist (μ ᵥ* P ^ (t + 1)) ν = tvDist ((μ ᵥ* P ^ t) ᵥ* P) (ν ᵥ* P) := by
        rw [hν, _root_.pow_succ, Matrix.vecMul_vecMul]
    _ ≤ tvDist (μ ᵥ* P ^ t) ν := tvDist_vecMul_le hP _ _

theorem antitone_tvDist_vecMul_pow (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ} (hν : ν ᵥ* P = ν)
    (μ : Ω → ℝ) : Antitone fun t : ℕ => tvDist (μ ᵥ* P ^ t) ν :=
  antitone_nat_of_succ_le fun t => tvDist_vecMul_pow_succ_le hP hν μ t

/-- The distance of the row `(P ^ t) x` from a stationary `ν` is nonincreasing in `t`. -/
theorem antitone_tvDist_pow_row (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ} (hν : ν ᵥ* P = ν)
    (x : Ω) : Antitone fun t : ℕ => tvDist ((P ^ t) x) ν :=
  antitone_nat_of_succ_le fun t =>
    calc tvDist ((P ^ (t + 1)) x) ν = tvDist ((P ^ t) x ᵥ* P) (ν ᵥ* P) := by
          rw [hν, pow_succ_row]
      _ ≤ tvDist ((P ^ t) x) ν := tvDist_vecMul_le hP _ _

/-- The worst-case distance `d(t) = max_x ‖P^t(x, ·) - ν‖_TV` is nonincreasing. -/
theorem antitone_sup_tvDist_pow_row [Nonempty Ω] (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ}
    (hν : ν ᵥ* P = ν) :
    Antitone fun t : ℕ => Finset.univ.sup' Finset.univ_nonempty fun x => tvDist ((P ^ t) x) ν :=
  antitone_nat_of_succ_le fun t =>
    Finset.sup'_le _ _ fun x hx =>
      (antitone_tvDist_pow_row hP hν x (Nat.le_succ t)).trans
        (Finset.le_sup' (fun x => tvDist ((P ^ t) x) ν) hx)

section HeatBath

omit [DecidableEq Ω] in
/-- The **heat-bath (Glauber) kernel**: from `x`, resample within the `R`-class of `x`
proportionally to `w`. A site update `y ↦ w y / ∑_{z ~ᵢ x} w z` on configurations agreeing off
a site `i` is `heatBath (sameExcept i) w` by `rfl`. -/
def heatBath (R : Ω → Ω → Prop) [DecidableRel R] (w : Ω → ℝ) : Matrix Ω Ω ℝ := fun x y =>
  if R x y then w y / ∑ z, (if R x z then w z else 0) else 0

omit [DecidableEq Ω] in
lemma sum_heatBath {R : Ω → Ω → Prop} [DecidableRel R] {w : Ω → ℝ} (hR : ∀ x, R x x)
    (hw : ∀ x, 0 < w x) (x : Ω) : ∑ y, heatBath R w x y = 1 := by
  have hZ : 0 < ∑ z, (if R x z then w z else 0) :=
    lt_of_lt_of_le (by simpa [hR x] using hw x)
      (Finset.single_le_sum (f := fun z => if R x z then w z else 0)
        (fun z _ => by split_ifs <;> simp [(hw z).le]) (Finset.mem_univ x))
  have h : ∀ y, heatBath R w x y = (if R x y then w y else 0) / ∑ z, (if R x z then w z else 0) :=
    fun y => by unfold heatBath; split_ifs <;> simp
  simp only [h, ← Finset.sum_div]
  exact div_self hZ.ne'

lemma heatBath_mem_rowStochastic {R : Ω → Ω → Prop} [DecidableRel R] {w : Ω → ℝ}
    (hR : ∀ x, R x x) (hw : ∀ x, 0 < w x) : heatBath R w ∈ rowStochastic ℝ Ω := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun x y => ?_, sum_heatBath hR hw⟩
  unfold heatBath
  split_ifs
  · exact div_nonneg (hw y).le
      (Finset.sum_nonneg fun z _ => by split_ifs <;> simp [(hw z).le])
  · exact le_rfl

omit [DecidableEq Ω] in
/-- The heat-bath kernel of an equivalence relation is reversible for `w`. -/
theorem heatBath_detailedBalance {R : Ω → Ω → Prop} [DecidableRel R] (hR : Equivalence R)
    (w : Ω → ℝ) (x y : Ω) : w x * heatBath R w x y = w y * heatBath R w y x := by
  unfold heatBath
  by_cases hxy : R x y
  · have hZ : ∑ z, (if R x z then w z else 0) = ∑ z, (if R y z then w z else 0) :=
      Finset.sum_congr rfl fun z _ => by
        have : R x z ↔ R y z := ⟨hR.trans (hR.symm hxy), hR.trans hxy⟩
        simp only [this]
    simp only [hxy, hR.symm hxy, ite_true, hZ]
    ring
  · have hyx : ¬R y x := fun h => hxy (hR.symm h)
    simp [hxy, hyx]

omit [DecidableEq Ω] in
/-- The weights `w` are stationary for their heat-bath kernel. -/
theorem vecMul_heatBath {R : Ω → Ω → Prop} [DecidableRel R] (hR : Equivalence R)
    {w : Ω → ℝ} (hw : ∀ x, 0 < w x) : w ᵥ* heatBath R w = w :=
  vecMul_eq_of_detailedBalance (sum_heatBath hR.refl hw) (heatBath_detailedBalance hR w)

end HeatBath

/-- The uniform average `n⁻¹ ∑ i, K i` of `n ≠ 0` kernels is a kernel. -/
lemma inv_natCast_smul_sum_mem_rowStochastic {n : ℕ} [NeZero n]
    {K : Fin n → Matrix Ω Ω ℝ} (hK : ∀ i, K i ∈ rowStochastic ℝ Ω) :
    (n : ℝ)⁻¹ • ∑ i, K i ∈ rowStochastic ℝ Ω := by
  simpa using inv_card_smul_sum_mem_rowStochastic hK

omit [DecidableEq Ω] in
/-- A vector stationary for each of `K i` is stationary for their average. -/
lemma vecMul_inv_card_smul_sum {ι : Type*} [Fintype ι] [Nonempty ι] {K : ι → Matrix Ω Ω ℝ}
    {ν : Ω → ℝ} (hK : ∀ i, ν ᵥ* K i = ν) : ν ᵥ* ((Fintype.card ι : ℝ)⁻¹ • ∑ i, K i) = ν := by
  rw [Matrix.vecMul_smul, Matrix.vecMul_sum]
  simp only [hK, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]

omit [DecidableEq Ω] in
lemma vecMul_inv_natCast_smul_sum {n : ℕ} [NeZero n] {K : Fin n → Matrix Ω Ω ℝ} {ν : Ω → ℝ}
    (hK : ∀ i, ν ᵥ* K i = ν) : ν ᵥ* ((n : ℝ)⁻¹ • ∑ i, K i) = ν := by
  simpa using vecMul_inv_card_smul_sum hK

end MarkovChain

end

end TheoremOS.Probability
