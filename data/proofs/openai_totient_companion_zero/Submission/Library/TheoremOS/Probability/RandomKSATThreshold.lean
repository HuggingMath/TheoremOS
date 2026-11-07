import Submission.Library.TheoremOS.Probability.RandomKSAT

/-!
# Random k-SAT: the first-moment density

The first-moment upper bound on the random `k`-SAT threshold. Contents: the density
`ksatFirstMomentDensity k = log 2 / (-log (1 - 2^{-k}))`; `b^n q^⌊c n⌋ → 0` for `0 < q < 1` and
`c > log b / (-log q)` (`tendsto_pow_mul_pow_floor`), in particular
`2^n (1 - 2^{-k})^⌊c n⌋ → 0` above the density; so with `⌊c n⌋` uniform random clauses of width
`k ≥ 1` the fraction of satisfiable sign-vector formulas tends to `0`, and under the uniform
clause stream the probability that the first `⌊c n⌋` clauses are satisfiable tends to `0`, for any
clause model with `C(n,k) 2^k` clauses of which each assignment satisfies `C(n,k) (2^k - 1)`.

Sources: J. Franco and M. Paull, "Probabilistic analysis of the Davis–Putnam procedure for solving
the satisfiability problem", Discrete Appl. Math. 5 (1983), 77–87; V. Chvátal and B. Reed, "Mick
gets some (the odds are on his side)", FOCS 1992; D. Achlioptas, "Random satisfiability", Chapter 8
of *Handbook of Satisfiability*, IOS Press, 2009 (the bound `r_k ≤ 2^k log 2`). Textbook material;
nothing here is specific to a benchmark problem.

Bridges: `log 2 / (-log (1 - ((2 : ℝ) ^ k)⁻¹))` is `ksatFirstMomentDensity k` by `rfl`. The
counting and stream statements reuse the clause models of `TheoremOS.Probability.RandomKSAT`.
-/

namespace TheoremOS.Probability

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

/-- The **first-moment density** of random `k`-SAT, `log 2 / (-log (1 - 2^{-k}))`: above it the
expected number of satisfying assignments of a formula with `c n` clauses tends to `0`. -/
def ksatFirstMomentDensity (k : ℕ) : ℝ := Real.log 2 / (-Real.log (1 - ((2 : ℝ) ^ k)⁻¹))

/-- `b^n q^⌊c n⌋ → 0` when `0 < q < 1` and `c > log b / (-log q)`. -/
lemma tendsto_pow_mul_pow_floor {b q c : ℝ} (hb : 0 < b) (hq0 : 0 < q) (hq1 : q < 1)
    (hc : Real.log b / (-Real.log q) < c) :
    Tendsto (fun n : ℕ => b ^ n * q ^ ⌊c * n⌋₊) atTop (𝓝 0) := by
  have hL : 0 < -Real.log q := neg_pos.2 (Real.log_neg hq0 hq1)
  set ε := c * (-Real.log q) - Real.log b with hε
  have hε0 : 0 < ε := by
    rw [div_lt_iff₀ hL] at hc
    linarith
  have hbound : ∀ n : ℕ, b ^ n * q ^ ⌊c * n⌋₊ ≤ q⁻¹ * Real.exp (-ε) ^ n := fun n => by
    have hfl : c * n - 1 ≤ (⌊c * n⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one (c * n)
      rcases le_or_gt 0 (c * n) with h0 | h0
      · linarith
      · have : (0 : ℝ) ≤ ⌊c * n⌋₊ := Nat.cast_nonneg _
        linarith
    have hqm : q ^ ⌊c * n⌋₊ ≤ Real.exp ((c * n - 1) * Real.log q) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq0, Real.exp_le_exp, mul_comm]
      exact mul_le_mul_of_nonpos_right hfl (Real.log_neg hq0 hq1).le
    have hbn : b ^ n = Real.exp (n * Real.log b) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hb, mul_comm]
    calc b ^ n * q ^ ⌊c * n⌋₊
        ≤ Real.exp (n * Real.log b) * Real.exp ((c * n - 1) * Real.log q) := by
          rw [hbn]
          gcongr
      _ = q⁻¹ * Real.exp (-ε) ^ n := by
          rw [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_log (inv_pos.2 hq0), ← Real.exp_add,
            Real.log_inv, hε]
          congr 1
          ring
  have ht : Tendsto (fun n : ℕ => q⁻¹ * Real.exp (-ε) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (neg_neg_of_pos hε0))).const_mul q⁻¹
  exact squeeze_zero (fun n => by positivity) hbound ht

/-- Above the first-moment density, `2^n (1 - 2^{-k})^⌊c n⌋ → 0`. -/
lemma tendsto_two_pow_mul_pow_floor {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (hc : ksatFirstMomentDensity k < c) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ ⌊c * n⌋₊) atTop (𝓝 0) := by
  have h2 : (2 : ℝ) ≤ 2 ^ k := by simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have hi : ((2 : ℝ) ^ k)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hi0 : 0 < ((2 : ℝ) ^ k)⁻¹ := by positivity
  exact tendsto_pow_mul_pow_floor two_pos (by linarith) (by linarith) hc

/-- Above the first-moment density, random `k`-SAT with sign-vector clauses and `⌊c n⌋` clauses
is unsatisfiable with probability tending to `1`. -/
lemma tendsto_natCard_signClause_satisfiable_div {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (hc : ksatFirstMomentDensity k < c) :
    Tendsto (fun n : ℕ =>
      (Nat.card {F : Fin ⌊c * n⌋₊ → SignClause n k // ∃ a, ∀ j, (F j).Sat a} : ℝ) /
        Nat.card (Fin ⌊c * n⌋₊ → SignClause n k)) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity)
    ((eventually_ge_atTop k).mono fun n hn => natCard_signClause_satisfiable_div_le hn _)
    (tendsto_two_pow_mul_pow_floor hk hc)

/-- Above the first-moment density, under the uniform clause stream of any clause model with
`C(n,k) 2^k` clauses of which each assignment satisfies `C(n,k) (2^k - 1)`, the first `⌊c n⌋`
clauses are satisfiable with probability tending to `0`. -/
lemma tendsto_infinitePi_uniformOn_exists_forall_sat {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (hc : ksatFirstMomentDensity k < c) (C : ℕ → Type*) [∀ n, Fintype (C n)]
    [∀ n, MeasurableSpace (C n)] [∀ n, MeasurableSingletonClass (C n)]
    (sat : ∀ n, C n → (Fin n → Bool) → Prop) (hN : ∀ n, Nat.card (C n) = n.choose k * 2 ^ k)
    (hs : ∀ n a, Nat.card {x // sat n x a} = n.choose k * (2 ^ k - 1)) :
    Tendsto (fun n : ℕ => (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set (C n)))
      {ω | ∃ a, ∀ i < ⌊c * n⌋₊, sat n (ω i) a}).toReal) atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    ((eventually_ge_atTop k).mono fun n hn =>
      infinitePi_uniformOn_exists_forall_sat_le_of_natCard (sat n) hn (hN n) (hs n) _)
    (tendsto_two_pow_mul_pow_floor hk hc)

end

end TheoremOS.Probability
