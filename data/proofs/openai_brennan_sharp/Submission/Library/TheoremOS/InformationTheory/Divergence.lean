import Submission.Library.TheoremOS.Probability.Concentration
import Submission.Library.TheoremOS.Probability.Dobrushin

/-!
# Relative entropy, Pinsker and two-point bounds

Finite-distribution facts about `relEntropy p q = ∑ ω, p ω log (p ω / q ω)`. Contents: the
data-processing inequality for a map (`relEntropy_pushforward_le`) and for a row-stochastic kernel
(`relEntropy_vecMul_le`); the Gibbs variational bound `E_p X - log E_q e^X ≤ D(p‖q)`; **Pinsker's
inequality** `2 tvDist(p, q)² ≤ D(p‖q)` and its two-point form `2 (a - b)² ≤ klBernoulli a b`;
the Bhattacharyya bound `e^{-D/2} ≤ ∑ √(p q)`, **Le Cam's inequality** `e^{-D} ≤ 1 - tvDist²` and
the **Bretagnolle–Huber inequality** `e^{-D} / 2 ≤ 1 - tvDist`; the χ² divergence with
`D ≤ χ²` and `tvDist ≤ √χ² / 2`; additivity of `relEntropy` on products; mutual information as
`relEntropy` against the product of the marginals, its nonnegativity and the identity
`I = H(X) + H(Y) - H(X, Y)`; and `D(p‖uniform) = log |Ω| - H(p)`.

Every general `relEntropy p q` statement carries the absolute continuity hypothesis
`∀ ω, q ω = 0 → p ω = 0`. Without it the junk value `log 0 = 0` makes `relEntropy` meaningless,
so check it before applying a lemma. The exceptions are cases where it holds automatically:
`pinsker_bernoulli` (it asks `0 < b < 1`), mutual information (the product of the marginals
vanishes only where `r` does, `marginal_mul_eq_zero`) and `relEntropy_uniform`.

Sources: T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
Sections 2.3–2.8 and 11.6; A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
2009, Section 2.4 (Lemmas 2.5–2.6); J. Bretagnolle and C. Huber, Estimation des densités : risque
minimax, Z. Wahrsch. Verw. Gebiete 47 (1979). The Pinsker proof here goes through the Gibbs
variational bound and Hoeffding's lemma for one Bernoulli variable. Textbook material; nothing
here is specific to a benchmark problem.

Bridges: `klBernoulli a b` is `relEntropy` of two-point laws (`klBernoulli_eq_relEntropy`), so
`pinsker_bernoulli` reads directly. For a lower bound on a test's error, combine
`bretagnolle_huber` with `prob_sub_prob_le_tvDist`: any event `s` has
`prob p s + prob q sᶜ ≥ 1 - tvDist p q ≥ e^{-D(p‖q)} / 2`. For product laws
`relEntropy_prod` adds the per-coordinate divergences.
-/

namespace TheoremOS.InformationTheory

open Finset Matrix Real
open TheoremOS.Probability
open scoped BigOperators

noncomputable section

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

section DataProcessing

/-- The log-sum inequality on a sub-`Finset`. -/
theorem sum_mul_log_div_le_of_finset (s : Finset Ω) {a b : Ω → ℝ} (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i) (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i ∈ s, a i) * log ((∑ i ∈ s, a i) / ∑ i ∈ s, b i) ≤ ∑ i ∈ s, a i * log (a i / b i) := by
  classical
  have h := sum_mul_log_div_le (a := fun i => if i ∈ s then a i else 0)
    (b := fun i => if i ∈ s then b i else 0)
    (fun i => by split_ifs <;> simp [ha i]) (fun i => by split_ifs <;> simp [hb i])
    (fun i => by split_ifs with hi <;> simp_all)
  have e : ∀ e : Ω → ℝ, ∑ i, (if i ∈ s then e i else 0) = ∑ i ∈ s, e i :=
    fun e => Fintype.sum_ite_mem s e
  have e' : ∀ i, (if i ∈ s then a i else 0) * log ((if i ∈ s then a i else 0) /
      if i ∈ s then b i else 0) = if i ∈ s then a i * log (a i / b i) else 0 := fun i => by
    split_ifs <;> simp
  simp only [e', e] at h
  exact h

/-- **Data processing**: relative entropy does not increase under a map. -/
theorem relEntropy_pushforward_le [DecidableEq Ω'] (f : Ω → Ω') {p q : Ω → ℝ}
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω) (hpq : ∀ ω, q ω = 0 → p ω = 0) :
    relEntropy (pushforward f p) (pushforward f q) ≤ relEntropy p q := by
  unfold relEntropy pushforward
  calc ∑ y, (∑ ω with f ω = y, p ω) * log ((∑ ω with f ω = y, p ω) / ∑ ω with f ω = y, q ω)
      ≤ ∑ y, ∑ ω with f ω = y, p ω * log (p ω / q ω) :=
        Finset.sum_le_sum fun y _ => sum_mul_log_div_le_of_finset _ hp hq hpq
    _ = ∑ ω, p ω * log (p ω / q ω) := Finset.sum_fiberwise Finset.univ f _

/-- **Data processing**: relative entropy does not increase under a row-stochastic kernel. -/
theorem relEntropy_vecMul_le {K : Matrix Ω Ω' ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hrow : ∀ x, ∑ y, K x y = 1) {p q : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) :
    relEntropy (p ᵥ* K) (q ᵥ* K) ≤ relEntropy p q := by
  have hterm : ∀ x y, p x * K x y * log (p x * K x y / (q x * K x y)) =
      K x y * (p x * log (p x / q x)) := fun x y => by
    rcases (hK x y).eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · rw [mul_div_mul_right _ _ hpos.ne']; ring
  have h1 : ∀ y, (p ᵥ* K) y * log ((p ᵥ* K) y / (q ᵥ* K) y) ≤
      ∑ x, K x y * (p x * log (p x / q x)) := fun y => by
    have h := sum_mul_log_div_le (a := fun x => p x * K x y) (b := fun x => q x * K x y)
      (fun x => mul_nonneg (hp x) (hK x y)) (fun x => mul_nonneg (hq x) (hK x y))
      (fun x hx => by
        rcases mul_eq_zero.mp hx with h | h
        · rw [hpq x h, zero_mul]
        · rw [h, mul_zero])
    simp only [hterm] at h
    simpa only [Matrix.vecMul, dotProduct] using h
  calc relEntropy (p ᵥ* K) (q ᵥ* K) ≤ ∑ y, ∑ x, K x y * (p x * log (p x / q x)) :=
        Finset.sum_le_sum fun y _ => h1 y
    _ = relEntropy p q := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, hrow, one_mul, relEntropy]

end DataProcessing

section Pinsker

/-- The **Gibbs variational bound** (Donsker–Varadhan): `E_p X - log E_q e^X ≤ D(p‖q)`. -/
theorem expectation_sub_log_le_relEntropy {p q : Ω → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) (hpq : ∀ ω, q ω = 0 → p ω = 0) (X : Ω → ℝ) :
    expectation p X - log (∑ ω, q ω * exp (X ω)) ≤ relEntropy p q := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ ω, q ω * exp (X ω) := ⟨_, rfl⟩
  rw [← hZ]
  have hZpos : 0 < Z := by
    obtain ⟨ω, hω⟩ : ∃ ω, 0 < q ω := by
      by_contra h
      have : ∑ ω, q ω ≤ 0 := Finset.sum_nonpos fun ω _ => not_lt.1 fun hω => h ⟨ω, hω⟩
      linarith [hq.sum_eq_one]
    rw [hZ]
    calc 0 < q ω * exp (X ω) := mul_pos hω (exp_pos _)
      _ ≤ ∑ ω, q ω * exp (X ω) := Finset.single_le_sum
          (fun ω _ => mul_nonneg (hq.nonneg ω) (exp_pos _).le) (Finset.mem_univ ω)
  have hr : IsDistribution fun ω => q ω * exp (X ω) / Z :=
    ⟨fun ω => div_nonneg (mul_nonneg (hq.nonneg ω) (exp_pos _).le) hZpos.le, by
      show ∑ ω, q ω * exp (X ω) / Z = 1
      rw [← Finset.sum_div, ← hZ, div_self hZpos.ne']⟩
  have hpr : ∀ ω, q ω * exp (X ω) / Z = 0 → p ω = 0 := fun ω h => by
    rcases div_eq_zero_iff.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hpq ω h
      · exact absurd h (exp_pos _).ne'
    · exact absurd h hZpos.ne'
  have h0 := relEntropy_nonneg hp hr hpr
  have key : ∀ ω, p ω * log (p ω / (q ω * exp (X ω) / Z)) =
      p ω * log (p ω / q ω) - p ω * X ω + p ω * log Z := fun ω => by
    by_cases h0 : p ω = 0
    · simp [h0]
    have hq0 : q ω ≠ 0 := fun h => h0 (hpq ω h)
    rw [div_div_eq_mul_div, log_div (mul_ne_zero h0 hZpos.ne') (mul_ne_zero hq0 (exp_pos _).ne'),
      log_mul h0 hZpos.ne', log_mul hq0 (exp_pos _).ne', log_exp, log_div h0 hq0]
    ring
  have hsum : relEntropy p (fun ω => q ω * exp (X ω) / Z) =
      relEntropy p q - expectation p X + log Z := by
    simp only [relEntropy, key, Finset.sum_add_distrib, Finset.sum_sub_distrib, expectation,
      ← Finset.sum_mul, hp.sum_eq_one, one_mul]
  linarith

/-- **Pinsker's inequality**: `2 tvDist(p, q)² ≤ D(p‖q)`. -/
theorem pinsker [DecidableEq Ω] {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) : 2 * tvDist p q ^ 2 ≤ relEntropy p q := by
  obtain ⟨A, hA⟩ : ∃ A : Finset Ω, A = ({ω | q ω < p ω} : Finset Ω) := ⟨_, rfl⟩
  have hgap : prob p A - prob q A = tvDist p q := by
    rw [hA]; exact prob_sub_prob_lt_eq_tvDist (by rw [hp.sum_eq_one, hq.sum_eq_one])
  obtain ⟨t, ht⟩ : ∃ t, t = tvDist p q := ⟨_, rfl⟩
  rw [← ht] at hgap ⊢
  have ht0 : 0 ≤ t := ht ▸ tvDist_nonneg p q
  obtain ⟨a, ha⟩ : ∃ a, a = prob q A := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ prob_nonneg hq.nonneg A
  have ha1 : a ≤ 1 := ha ▸ prob_le_one hq A
  have h := expectation_sub_log_le_relEntropy hp hq hpq fun ω => if ω ∈ A then 4 * t else 0
  have hE : expectation p (fun ω => if ω ∈ A then 4 * t else 0) = 4 * t * prob p A := by
    rw [expectation, prob, Finset.mul_sum, ← Fintype.sum_ite_mem A]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs
    · ring
    · ring
  have hZ : ∑ ω, q ω * exp (if ω ∈ A then 4 * t else 0) = a * exp (4 * t) + (1 - a) := by
    have : ∀ ω, q ω * exp (if ω ∈ A then 4 * t else 0) =
        q ω + if ω ∈ A then q ω * (exp (4 * t) - 1) else 0 := fun ω => by
      split_ifs
      · ring
      · simp
    simp only [this, Finset.sum_add_distrib, Fintype.sum_ite_mem, ← Finset.sum_mul,
      hq.sum_eq_one]
    rw [ha, prob]
    ring
  have hb := bernoulli_exp_le ha0 ha1 (4 * t)
  have hexp : a * exp (4 * t) + (1 - a) ≤ exp (4 * t * a + 2 * t ^ 2) := by
    have e0 : exp (4 * t * (1 - a)) = exp (4 * t) * exp (-(4 * t * a)) := by
      rw [← exp_add]; congr 1; ring
    have e1 : a * exp (4 * t * (1 - a)) + (1 - a) * exp (-(4 * t * a)) =
        (a * exp (4 * t) + (1 - a)) * exp (-(4 * t * a)) := by
      rw [e0]; ring
    have e2 : exp ((4 * t) ^ 2 / 8) = exp (4 * t * a + 2 * t ^ 2) * exp (-(4 * t * a)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2] at hb
    exact le_of_mul_le_mul_right hb (exp_pos _)
  have hpos : 0 < a * exp (4 * t) + (1 - a) := by
    have := one_le_exp (by linarith : (0 : ℝ) ≤ 4 * t)
    nlinarith
  have hlog : log (a * exp (4 * t) + (1 - a)) ≤ 4 * t * a + 2 * t ^ 2 := by
    calc log (a * exp (4 * t) + (1 - a)) ≤ log (exp (4 * t * a + 2 * t ^ 2)) :=
          log_le_log hpos hexp
      _ = 4 * t * a + 2 * t ^ 2 := log_exp _
  rw [hE, hZ] at h
  have hpA : prob p A = a + t := by linarith
  rw [hpA] at h
  nlinarith

/-- **Pinsker's inequality**, square-root form: `tvDist p q ≤ √(D(p‖q) / 2)`. -/
theorem tvDist_le_sqrt_relEntropy [DecidableEq Ω] {p q : Ω → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) (hpq : ∀ ω, q ω = 0 → p ω = 0) :
    tvDist p q ≤ √(relEntropy p q / 2) :=
  le_sqrt_of_sq_le (by linarith [pinsker hp hq hpq])

/-- Two-point **Pinsker**: `2 (a - b)² ≤ klBernoulli a b`. -/
theorem pinsker_bernoulli {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ klBernoulli a b := by
  have hd : ∀ {c : ℝ}, 0 ≤ c → c ≤ 1 → IsDistribution fun x : Bool => if x then c else 1 - c :=
    fun hc0 hc1 => ⟨fun x => by cases x <;> simp <;> linarith, by rw [Fintype.sum_bool]; simp⟩
  have h := pinsker (hd ha0 ha1) (hd hb0.le hb1.le) fun x hx => by
    cases x <;> simp at hx ⊢ <;> linarith
  have htv : tvDist (fun x : Bool => if x then a else 1 - a) (fun x => if x then b else 1 - b) =
      |a - b| := by
    rw [tvDist, Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [show 1 - a - (1 - b) = -(a - b) by ring, abs_neg]
    ring
  rw [klBernoulli_eq_relEntropy, ← sq_abs (a - b), ← htv]
  exact h

/-- The **Bhattacharyya bound** `e^{-D(p‖q)/2} ≤ ∑ √(p q)`. -/
theorem exp_neg_relEntropy_div_two_le {p q : Ω → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) (hpq : ∀ ω, q ω = 0 → p ω = 0) :
    exp (-(relEntropy p q / 2)) ≤ ∑ ω, √(p ω * q ω) := by
  obtain ⟨s, hs⟩ : ∃ s, s = ∑ ω, √(p ω * q ω) := ⟨_, rfl⟩
  rw [← hs]
  have hspos : 0 < s := by
    obtain ⟨ω, hω⟩ : ∃ ω, 0 < p ω := by
      by_contra h
      have : ∑ ω, p ω ≤ 0 := Finset.sum_nonpos fun ω _ => not_lt.1 fun hω => h ⟨ω, hω⟩
      linarith [hp.sum_eq_one]
    have hqω : 0 < q ω := lt_of_le_of_ne (hq.nonneg ω) fun h => hω.ne' (hpq ω h.symm)
    rw [hs]
    calc 0 < √(p ω * q ω) := sqrt_pos.2 (mul_pos hω hqω)
      _ ≤ ∑ ω, √(p ω * q ω) := Finset.single_le_sum (f := fun ω => √(p ω * q ω))
          (fun ω _ => sqrt_nonneg _) (Finset.mem_univ ω)
  have hr : IsDistribution fun ω => √(p ω * q ω) / s :=
    ⟨fun ω => div_nonneg (sqrt_nonneg _) hspos.le, by
      show ∑ ω, √(p ω * q ω) / s = 1
      rw [← Finset.sum_div, ← hs, div_self hspos.ne']⟩
  have hpr : ∀ ω, √(p ω * q ω) / s = 0 → p ω = 0 := fun ω h => by
    rcases div_eq_zero_iff.mp h with h | h
    · rcases mul_eq_zero.mp ((sqrt_eq_zero (mul_nonneg (hp.nonneg ω) (hq.nonneg ω))).mp h)
        with h | h
      · exact h
      · exact hpq ω h
    · exact absurd h hspos.ne'
  have h0 := relEntropy_nonneg hp hr hpr
  have key : ∀ ω, p ω * log (p ω / (√(p ω * q ω) / s)) =
      p ω * log (p ω / q ω) / 2 + p ω * log s := fun ω => by
    by_cases h0 : p ω = 0
    · simp [h0]
    have hp0 : 0 < p ω := lt_of_le_of_ne (hp.nonneg ω) (Ne.symm h0)
    have hq0 : 0 < q ω := lt_of_le_of_ne (hq.nonneg ω) fun h => h0 (hpq ω h.symm)
    have hsq : 0 < √(p ω * q ω) := sqrt_pos.2 (mul_pos hp0 hq0)
    rw [div_div_eq_mul_div, log_div (mul_ne_zero h0 hspos.ne') hsq.ne', log_mul h0 hspos.ne',
      log_sqrt (mul_nonneg hp0.le hq0.le), log_mul h0 hq0.ne', log_div h0 hq0.ne']
    ring
  have hsum : relEntropy p (fun ω => √(p ω * q ω) / s) = relEntropy p q / 2 + log s := by
    simp only [relEntropy, key, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
      hp.sum_eq_one, one_mul]
  have hlog : -(relEntropy p q / 2) ≤ log s := by linarith
  calc exp (-(relEntropy p q / 2)) ≤ exp (log s) := exp_le_exp.2 hlog
    _ = s := exp_log hspos

/-- **Le Cam's inequality** `e^{-D(p‖q)} ≤ 1 - tvDist(p, q)²`. -/
theorem exp_neg_relEntropy_le_one_sub_sq {p q : Ω → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) (hpq : ∀ ω, q ω = 0 → p ω = 0) :
    exp (-relEntropy p q) ≤ 1 - tvDist p q ^ 2 := by
  have hB := exp_neg_relEntropy_div_two_le hp hq hpq
  have hmin := tvDist_eq_one_sub_sum_min hp hq
  have hmax : ∑ ω, max (p ω) (q ω) = 1 + tvDist p q := by
    have e : ∀ ω, max (p ω) (q ω) = p ω + q ω - min (p ω) (q ω) := fun ω => by
      have := min_add_max (p ω) (q ω)
      linarith
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.sum_eq_one, hq.sum_eq_one]
    linarith
  have hmn : ∀ ω, 0 ≤ min (p ω) (q ω) := fun ω => le_min (hp.nonneg ω) (hq.nonneg ω)
  have hmx : ∀ ω, 0 ≤ max (p ω) (q ω) := fun ω => (hp.nonneg ω).trans (le_max_left _ _)
  have hcs : (∑ ω, √(p ω * q ω)) ^ 2 ≤
      (∑ ω, min (p ω) (q ω)) * ∑ ω, max (p ω) (q ω) := by
    have e : ∀ ω, √(p ω * q ω) = √(min (p ω) (q ω)) * √(max (p ω) (q ω)) := fun ω => by
      rw [← sqrt_mul (hmn ω), min_mul_max]
    have hs1 : ∀ ω, √(min (p ω) (q ω)) ^ 2 = min (p ω) (q ω) := fun ω => sq_sqrt (hmn ω)
    have hs2 : ∀ ω, √(max (p ω) (q ω)) ^ 2 = max (p ω) (q ω) := fun ω => sq_sqrt (hmx ω)
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ω => √(min (p ω) (q ω)))
      fun ω => √(max (p ω) (q ω))
    simp only [hs1, hs2] at h
    simp only [e]
    exact h
  have hB0 : 0 ≤ exp (-(relEntropy p q / 2)) := (exp_pos _).le
  calc exp (-relEntropy p q) = exp (-(relEntropy p q / 2)) ^ 2 := by
        rw [sq, ← exp_add]; congr 1; ring
    _ ≤ (∑ ω, √(p ω * q ω)) ^ 2 := pow_le_pow_left₀ hB0 hB 2
    _ ≤ (∑ ω, min (p ω) (q ω)) * ∑ ω, max (p ω) (q ω) := hcs
    _ = 1 - tvDist p q ^ 2 := by
        rw [hmax, show ∑ ω, min (p ω) (q ω) = 1 - tvDist p q by linarith]
        ring

/-- The **Bretagnolle–Huber inequality** `e^{-D(p‖q)} / 2 ≤ 1 - tvDist(p, q)`. -/
theorem bretagnolle_huber {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) : exp (-relEntropy p q) / 2 ≤ 1 - tvDist p q := by
  have h := exp_neg_relEntropy_le_one_sub_sq hp hq hpq
  have h0 := tvDist_nonneg p q
  have h1 := tvDist_le_one hp hq
  nlinarith [sq_nonneg (tvDist p q - 1)]

end Pinsker

section ChiSquare

/-- The χ² divergence `∑ (p - q)² / q`. -/
def chiSq (p q : Ω → ℝ) : ℝ := ∑ ω, (p ω - q ω) ^ 2 / q ω

lemma chiSq_eq {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) : chiSq p q = ∑ ω, p ω ^ 2 / q ω - 1 := by
  have e : ∀ ω, (p ω - q ω) ^ 2 / q ω = p ω ^ 2 / q ω - 2 * p ω + q ω := fun ω => by
    by_cases h : q ω = 0
    · simp [h, hpq ω h]
    · field_simp
      ring
  simp only [chiSq, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hp.sum_eq_one, hq.sum_eq_one]
  ring

/-- `D(p‖q) ≤ χ²(p‖q)`. -/
theorem relEntropy_le_chiSq {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) : relEntropy p q ≤ chiSq p q := by
  rw [chiSq_eq hp hq hpq, ← hp.sum_eq_one, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases h0 : p ω = 0
  · simp [h0]
  have hp0 : 0 < p ω := lt_of_le_of_ne (hp.nonneg ω) (Ne.symm h0)
  have hq0 : 0 < q ω := lt_of_le_of_ne (hq.nonneg ω) fun h => h0 (hpq ω h.symm)
  have hl := log_le_sub_one_of_pos (div_pos hp0 hq0)
  calc p ω * log (p ω / q ω) ≤ p ω * (p ω / q ω - 1) := mul_le_mul_of_nonneg_left hl hp0.le
    _ = p ω ^ 2 / q ω - p ω := by ring

/-- `tvDist p q ≤ √χ²(p‖q) / 2`. -/
theorem tvDist_le_sqrt_chiSq {p q : Ω → ℝ} (hq : IsDistribution q)
    (hpq : ∀ ω, q ω = 0 → p ω = 0) : tvDist p q ≤ √(chiSq p q) / 2 := by
  have e : ∀ ω, |p ω - q ω| = √(q ω) * (|p ω - q ω| / √(q ω)) := fun ω => by
    by_cases h : q ω = 0
    · simp [h, hpq ω h]
    · have : √(q ω) ≠ 0 := sqrt_ne_zero'.2 (lt_of_le_of_ne (hq.nonneg ω) (Ne.symm h))
      field_simp
  have hs : ∀ ω, (|p ω - q ω| / √(q ω)) ^ 2 = (p ω - q ω) ^ 2 / q ω := fun ω => by
    rw [div_pow, sq_abs, sq_sqrt (hq.nonneg ω)]
  have hq2 : ∀ ω, √(q ω) ^ 2 = q ω := fun ω => sq_sqrt (hq.nonneg ω)
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun ω => √(q ω))
    fun ω => |p ω - q ω| / √(q ω)
  simp only [hq2, hs, hq.sum_eq_one, sqrt_one, one_mul, ← e] at h
  rw [tvDist, chiSq]
  linarith

end ChiSquare

section Product

/-- Relative entropy adds on products. -/
theorem relEntropy_prod {p q : Ω → ℝ} {p' q' : Ω' → ℝ} (hp : IsDistribution p)
    (hp' : IsDistribution p') (hpq : ∀ ω, q ω = 0 → p ω = 0) (hpq' : ∀ ω, q' ω = 0 → p' ω = 0) :
    relEntropy (fun x : Ω × Ω' => p x.1 * p' x.2) (fun x => q x.1 * q' x.2) =
      relEntropy p q + relEntropy p' q' := by
  have e : ∀ a b, p a * p' b * log (p a * p' b / (q a * q' b)) =
      p' b * (p a * log (p a / q a)) + p a * (p' b * log (p' b / q' b)) := fun a b => by
    by_cases h1 : p a = 0
    · simp [h1]
    by_cases h2 : p' b = 0
    · simp [h2]
    have hq1 : q a ≠ 0 := fun h => h1 (hpq a h)
    have hq2 : q' b ≠ 0 := fun h => h2 (hpq' b h)
    rw [mul_div_mul_comm, log_mul (div_ne_zero h1 hq1) (div_ne_zero h2 hq2)]
    ring
  rw [relEntropy, Fintype.sum_prod_type]
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hp.sum_eq_one,
    hp'.sum_eq_one, one_mul, relEntropy]

end Product

section MutualInformation

/-- Mutual information of a joint law: `relEntropy` against the product of its marginals. -/
def mutualInfo (r : Ω × Ω' → ℝ) : ℝ :=
  relEntropy r fun x => marginalLeft r x.1 * marginalRight r x.2

variable {r : Ω × Ω' → ℝ}

lemma marginal_mul_eq_zero (hr : ∀ x, 0 ≤ r x) (x : Ω × Ω')
    (h : marginalLeft r x.1 * marginalRight r x.2 = 0) : r x = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact le_antisymm (h ▸ le_marginalLeft hr x) (hr x)
  · exact le_antisymm (h ▸ le_marginalRight hr x) (hr x)

theorem mutualInfo_nonneg (hr : IsDistribution r) : 0 ≤ mutualInfo r := by
  have h1 := hr.marginalLeft
  have h2 := hr.marginalRight
  have hq : IsDistribution fun x : Ω × Ω' => marginalLeft r x.1 * marginalRight r x.2 :=
    ⟨fun x => mul_nonneg (h1.nonneg _) (h2.nonneg _), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, h2.sum_eq_one, mul_one, h1.sum_eq_one]⟩
  exact relEntropy_nonneg hr hq (marginal_mul_eq_zero hr.nonneg)

/-- `I(X; Y) = H(X) + H(Y) - H(X, Y)`. -/
theorem mutualInfo_eq (hr : IsDistribution r) :
    mutualInfo r = entropy (marginalLeft r) + entropy (marginalRight r) - entropy r := by
  have hsupp := marginal_mul_eq_zero hr.nonneg
  have hlog : ∑ x : Ω × Ω', r x * log (marginalLeft r x.1 * marginalRight r x.2) =
      ∑ x : Ω × Ω', r x * log (marginalLeft r x.1) +
        ∑ x : Ω × Ω', r x * log (marginalRight r x.2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : r x = 0
    · simp [hx]
    have ha : marginalLeft r x.1 ≠ 0 := fun h => hx (hsupp x (by rw [h, zero_mul]))
    have hb : marginalRight r x.2 ≠ 0 := fun h => hx (hsupp x (by rw [h, mul_zero]))
    rw [log_mul ha hb, mul_add]
  have hleft : ∑ x : Ω × Ω', r x * log (marginalLeft r x.1) = -entropy (marginalLeft r) := by
    rw [entropy_eq_neg_sum, neg_neg, Fintype.sum_prod_type]
    simp only [marginalLeft, Finset.sum_mul]
  have hright : ∑ x : Ω × Ω', r x * log (marginalRight r x.2) = -entropy (marginalRight r) := by
    rw [entropy_eq_neg_sum, neg_neg, Fintype.sum_prod_type_right]
    simp only [marginalRight, Finset.sum_mul]
  rw [mutualInfo, relEntropy_eq_sub hsupp, hlog, hleft, hright, entropy_eq_neg_sum r]
  ring

end MutualInformation

/-- `D(p‖uniform) = log |Ω| - H(p)`. -/
theorem relEntropy_uniform [Nonempty Ω] {p : Ω → ℝ} (hp : IsDistribution p) :
    relEntropy p (uniform Ω) = log (Fintype.card Ω) - entropy p := by
  have hN : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hu : ∀ ω, uniform Ω ω = (Fintype.card Ω : ℝ)⁻¹ := fun _ => rfl
  rw [relEntropy_eq_sub fun ω h => absurd ((hu ω).symm.trans h) (inv_ne_zero hN),
    entropy_eq_neg_sum]
  simp only [hu, log_inv, mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul, hp.sum_eq_one,
    one_mul]
  ring

end

end TheoremOS.InformationTheory
