import Submission.Library.TheoremOS.Probability.FiniteProbability

/-!
# Dobrushin's ergodicity coefficient

For a matrix `P : Matrix Ω Ω' ℝ` with nonempty row index, `dobrushin P` is the largest total
variation distance between two rows. Contents: the overlap form `tvDist p q = 1 - ∑ min (p, q)`
of two distributions and the Doeblin bound it gives; Dobrushin's contraction
`tvDist (μ ᵥ* P) (ν ᵥ* P) ≤ dobrushin P * tvDist μ ν` for weights of equal mass (no sign
condition on `P`); `0 ≤ dobrushin P ≤ 1` for kernels, `dobrushin P = 0` iff all rows agree, and
`dobrushin P ≤ 1 - ε` under the minorization `ε ν ≤ P x` for all `x`; submultiplicativity
`dobrushin (P * Q) ≤ dobrushin P * dobrushin Q` and `dobrushin (P ^ t) ≤ dobrushin P ^ t`;
convergence to a stationary vector at rate `dobrushin P ^ t`, from a start state or a start
vector, and uniqueness of the stationary distribution when `dobrushin P < 1`; the comparison
`d(t) ≤ dobrushin (P ^ t) ≤ 2 d(t)` with the worst-case distance
`d(t) = max_x tvDist ((P ^ t) x) ν`, hence `d(k t) ≤ (2 d(t)) ^ k`.

Sources: D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS, 2017,
§4.3 (convergence under a Doeblin minorization), §4.4 (`d(t) ≤ d̄(t) ≤ 2 d(t)` and
submultiplicativity of `d̄`), §4.5 (`d(k t) ≤ (2 d(t)) ^ k`); E. Seneta, *Non-negative Matrices and
Markov Chains*, 2nd ed., Springer, 1981, Chapter 3 (coefficients of ergodicity); R. L. Dobrushin,
"Central limit theorem for nonstationary Markov chains I", Theory Probab. Appl. 1 (1956).
Textbook material; nothing here is specific to a benchmark problem.

Bridges: `dobrushin P` is `Finset.univ.sup' _ fun xy : Ω × Ω => tvDist (P xy.1) (P xy.2)`;
`dobrushin_le_iff` turns a bound on it into a bound on every pair of rows. `d̄(t)` in the sources
is `dobrushin (P ^ t)`. The row `(P * Q) x` is `P x ᵥ* Q` by `row_mul_eq_vecMul`.
-/

namespace TheoremOS.Probability

open Finset Matrix
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

variable {Ω Ω' Ω'' : Type*} [Fintype Ω] [Fintype Ω'] [Fintype Ω'']

section Overlap

lemma min_eq_add_sub_abs_div_two (a b : ℝ) : min a b = (a + b - |a - b|) / 2 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring

/-- The overlap form of total variation: `tvDist p q = 1 - ∑ min (p, q)`. -/
theorem tvDist_eq_one_sub_sum_min {p q : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    tvDist p q = 1 - ∑ ω, min (p ω) (q ω) := by
  simp only [min_eq_add_sub_abs_div_two, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp.sum_eq_one, hq.sum_eq_one, tvDist]
  ring

/-- **Doeblin bound**: weights below both distributions bound their distance by `1 - ∑ m`. -/
theorem tvDist_le_one_sub_sum {p q m : Ω → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hmp : ∀ ω, m ω ≤ p ω) (hmq : ∀ ω, m ω ≤ q ω) : tvDist p q ≤ 1 - ∑ ω, m ω := by
  rw [tvDist_eq_one_sub_sum_min hp hq]
  have : ∑ ω, m ω ≤ ∑ ω, min (p ω) (q ω) :=
    Finset.sum_le_sum fun ω _ => le_min (hmp ω) (hmq ω)
  linarith

end Overlap

section Coefficient

/-- **Dobrushin's ergodicity coefficient**: the largest total variation distance between two rows. -/
def dobrushin [Nonempty Ω] (P : Matrix Ω Ω' ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun xy : Ω × Ω => tvDist (P xy.1) (P xy.2)

variable [Nonempty Ω] {P : Matrix Ω Ω' ℝ}

lemma tvDist_row_le_dobrushin (P : Matrix Ω Ω' ℝ) (x y : Ω) :
    tvDist (P x) (P y) ≤ dobrushin P :=
  Finset.le_sup' (fun xy : Ω × Ω => tvDist (P xy.1) (P xy.2)) (Finset.mem_univ (x, y))

lemma dobrushin_le_iff {c : ℝ} : dobrushin P ≤ c ↔ ∀ x y, tvDist (P x) (P y) ≤ c := by
  refine ⟨fun h x y => (tvDist_row_le_dobrushin P x y).trans h, fun h => ?_⟩
  exact Finset.sup'_le _ _ fun xy _ => h xy.1 xy.2

lemma dobrushin_nonneg (P : Matrix Ω Ω' ℝ) : 0 ≤ dobrushin P := by
  obtain ⟨x⟩ := ‹Nonempty Ω›
  simpa using tvDist_row_le_dobrushin P x x

lemma dobrushin_le_one (hP : ∀ x, IsDistribution (P x)) : dobrushin P ≤ 1 :=
  dobrushin_le_iff.2 fun x y => tvDist_le_one (hP x) (hP y)

theorem dobrushin_eq_zero_iff : dobrushin P = 0 ↔ ∀ x y, P x = P y := by
  constructor
  · intro h x y
    have := tvDist_row_le_dobrushin P x y
    exact (tvDist_eq_zero_iff _ _).1 (le_antisymm (h ▸ this) (tvDist_nonneg _ _))
  · intro h
    refine le_antisymm (dobrushin_le_iff.2 fun x y => ?_) (dobrushin_nonneg P)
    rw [h x y, tvDist_self]

/-- **Doeblin minorization**: weights `m` below every row give `dobrushin P ≤ 1 - ∑ m`. -/
theorem dobrushin_le_one_sub_sum (hP : ∀ x, IsDistribution (P x)) {m : Ω' → ℝ}
    (hm : ∀ x y, m y ≤ P x y) : dobrushin P ≤ 1 - ∑ y, m y :=
  dobrushin_le_iff.2 fun x x' => tvDist_le_one_sub_sum (hP x) (hP x') (hm x) (hm x')

/-- The minorization `ε ν ≤ P x` by a distribution `ν` gives `dobrushin P ≤ 1 - ε`. -/
theorem dobrushin_le_one_sub (hP : ∀ x, IsDistribution (P x)) {ν : Ω' → ℝ} (hν : IsDistribution ν)
    {ε : ℝ} (hm : ∀ x y, ε * ν y ≤ P x y) : dobrushin P ≤ 1 - ε := by
  have := dobrushin_le_one_sub_sum hP hm
  rwa [← Finset.mul_sum, hν.sum_eq_one, mul_one] at this

/-- Any reference vector `ν` gives `dobrushin P ≤ 2 max_x tvDist (P x) ν`. -/
theorem dobrushin_le_two_mul_sup (P : Matrix Ω Ω' ℝ) (ν : Ω' → ℝ) :
    dobrushin P ≤ 2 * Finset.univ.sup' Finset.univ_nonempty fun x => tvDist (P x) ν := by
  refine dobrushin_le_iff.2 fun x x' => ?_
  have hx := Finset.le_sup' (fun x => tvDist (P x) ν) (Finset.mem_univ x)
  have hx' := Finset.le_sup' (fun x => tvDist (P x) ν) (Finset.mem_univ x')
  have := tvDist_triangle (P x) ν (P x')
  rw [tvDist_comm ν] at this
  linarith

end Coefficient

section Contraction

variable {P : Matrix Ω Ω' ℝ}

omit [Fintype Ω'] in
/-- The one-step identity behind the contraction: with `μ - ν = a - b`, `∑ a = ∑ b = T`,
`T ((μ ᵥ* P) y - (ν ᵥ* P) y) = ∑ x, ∑ x', a x * b x' * (P x y - P x' y)`. -/
lemma mul_vecMul_sub_vecMul {μ ν a b : Ω → ℝ} {T : ℝ} (hab : ∀ x, μ x - ν x = a x - b x)
    (hsa : ∑ x, a x = T) (hsb : ∑ x, b x = T) (y : Ω') :
    T * ((μ ᵥ* P) y - (ν ᵥ* P) y) = ∑ x, ∑ x', a x * b x' * (P x y - P x' y) := by
  have e1 : (μ ᵥ* P) y - (ν ᵥ* P) y = ∑ x, (a x - b x) * P x y := by
    simp only [Matrix.vecMul, dotProduct, ← Finset.sum_sub_distrib, ← sub_mul, hab]
  have r1 : ∀ x, ∑ x', a x * b x' * P x y = T * (a x * P x y) := fun x => by
    rw [← hsb, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x' _ => by ring
  have r2 : ∀ x', ∑ x, a x * b x' * P x' y = T * (b x' * P x' y) := fun x' => by
    rw [← hsa, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  calc T * ((μ ᵥ* P) y - (ν ᵥ* P) y)
      = ∑ x, T * (a x * P x y) - ∑ x, T * (b x * P x y) := by
        rw [e1, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ x, ∑ x', a x * b x' * P x y - ∑ x', ∑ x, a x * b x' * P x' y := by
        simp only [r1, r2]
    _ = ∑ x, ∑ x', a x * b x' * (P x y - P x' y) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_comm

/-- **Dobrushin's contraction**: if every two rows of `P` are within `δ` in total variation, then
`tvDist (μ ᵥ* P) (ν ᵥ* P) ≤ δ * tvDist μ ν` for weights of equal mass. -/
theorem tvDist_vecMul_le_mul {δ : ℝ} (hδ : ∀ x x', tvDist (P x) (P x') ≤ δ) {μ ν : Ω → ℝ}
    (h : ∑ x, μ x = ∑ x, ν x) : tvDist (μ ᵥ* P) (ν ᵥ* P) ≤ δ * tvDist μ ν := by
  rcases (tvDist_nonneg μ ν).eq_or_lt with h0 | hT
  · obtain rfl := (tvDist_eq_zero_iff μ ν).1 h0.symm
    simp
  set T := tvDist μ ν with hTdef
  obtain ⟨a, ha⟩ : ∃ a : Ω → ℝ, a = fun x => max (μ x - ν x) 0 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Ω → ℝ, b = fun x => max (ν x - μ x) 0 := ⟨_, rfl⟩
  have ha0 : ∀ x, 0 ≤ a x := fun x => by rw [ha]; exact le_max_right _ _
  have hb0 : ∀ x, 0 ≤ b x := fun x => by rw [hb]; exact le_max_right _ _
  have hsa : ∑ x, a x = T := by rw [hTdef, tvDist_eq_sum_max h, ha]
  have hsb : ∑ x, b x = T := by rw [hTdef, tvDist_comm, tvDist_eq_sum_max h.symm, hb]
  have hab : ∀ x, μ x - ν x = a x - b x := fun x => by
    rcases le_total 0 (μ x - ν x) with hx | hx
    · simp only [ha, hb, max_eq_left hx, max_eq_right (by linarith : ν x - μ x ≤ 0)]; ring
    · simp only [ha, hb, max_eq_right hx, max_eq_left (by linarith : 0 ≤ ν x - μ x)]; ring
  have hrow : ∀ x x', ∑ y, |P x y - P x' y| ≤ 2 * δ := fun x x' => by
    have := hδ x x'
    rw [tvDist] at this
    linarith
  have hδ0 : 0 ≤ δ := by
    rcases isEmpty_or_nonempty Ω with hne | hne
    · simp [hTdef, tvDist] at hT
    · obtain ⟨x⟩ := hne
      simpa using hδ x x
  have hbound : T * ∑ y, |(μ ᵥ* P) y - (ν ᵥ* P) y| ≤ T * T * (2 * δ) := by
    calc T * ∑ y, |(μ ᵥ* P) y - (ν ᵥ* P) y|
        = ∑ y, |∑ x, ∑ x', a x * b x' * (P x y - P x' y)| := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← mul_vecMul_sub_vecMul hab hsa hsb y, abs_mul, abs_of_nonneg hT.le]
      _ ≤ ∑ y, ∑ x, ∑ x', a x * b x' * |P x y - P x' y| := by
          refine Finset.sum_le_sum fun y _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun x _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun x' _ => le_of_eq ?_
          rw [abs_mul, abs_of_nonneg (mul_nonneg (ha0 x) (hb0 x'))]
      _ = ∑ x, ∑ x', a x * b x' * ∑ y, |P x y - P x' y| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ ∑ x, ∑ x', a x * b x' * (2 * δ) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ =>
            mul_le_mul_of_nonneg_left (hrow x x') (mul_nonneg (ha0 x) (hb0 x'))
      _ = T * T * (2 * δ) := by
          simp only [← Finset.sum_mul, ← Finset.mul_sum, hsa, hsb]
  have htv := tvDist_eq_sum_div_two (μ ᵥ* P) (ν ᵥ* P)
  have hle : T * tvDist (μ ᵥ* P) (ν ᵥ* P) ≤ T * (δ * T) := by
    rw [← htv]
    nlinarith
  exact le_of_mul_le_mul_left hle hT

/-- Dobrushin's contraction with the coefficient itself. -/
theorem tvDist_vecMul_le_dobrushin_mul [Nonempty Ω] (P : Matrix Ω Ω' ℝ) {μ ν : Ω → ℝ}
    (h : ∑ x, μ x = ∑ x, ν x) : tvDist (μ ᵥ* P) (ν ᵥ* P) ≤ dobrushin P * tvDist μ ν :=
  tvDist_vecMul_le_mul (tvDist_row_le_dobrushin P) h

/-- A matrix with unit row sums preserves total mass. -/
lemma sum_vecMul (hP : ∀ x, ∑ y, P x y = 1) (μ : Ω → ℝ) : ∑ y, (μ ᵥ* P) y = ∑ x, μ x := by
  simp only [Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hP, mul_one]

omit [Fintype Ω] [Fintype Ω''] in
lemma row_mul_eq_vecMul (P : Matrix Ω Ω' ℝ) (Q : Matrix Ω' Ω'' ℝ) (x : Ω) :
    (P * Q) x = P x ᵥ* Q := rfl

/-- **Submultiplicativity**: `dobrushin (P * Q) ≤ dobrushin P * dobrushin Q` when the rows of `P`
have equal sums (for instance, `P` is a kernel). -/
theorem dobrushin_mul_le [Nonempty Ω] [Nonempty Ω'] (hP : ∀ x, ∑ y, P x y = 1)
    (Q : Matrix Ω' Ω'' ℝ) : dobrushin (P * Q) ≤ dobrushin P * dobrushin Q := by
  refine dobrushin_le_iff.2 fun x x' => ?_
  rw [row_mul_eq_vecMul, row_mul_eq_vecMul]
  calc tvDist (P x ᵥ* Q) (P x' ᵥ* Q) ≤ dobrushin Q * tvDist (P x) (P x') :=
        tvDist_vecMul_le_dobrushin_mul Q (by rw [hP x, hP x'])
    _ ≤ dobrushin Q * dobrushin P :=
        mul_le_mul_of_nonneg_left (tvDist_row_le_dobrushin P x x') (dobrushin_nonneg Q)
    _ = dobrushin P * dobrushin Q := mul_comm _ _

omit [Fintype Ω'] in
/-- With `dobrushin P < 1`, two stationary vectors of equal mass coincide. -/
theorem eq_of_vecMul_eq_of_dobrushin_lt_one [Nonempty Ω] {P : Matrix Ω Ω ℝ}
    (hδ : dobrushin P < 1) {ν ν' : Ω → ℝ} (hν : ν ᵥ* P = ν) (hν' : ν' ᵥ* P = ν')
    (h : ∑ x, ν x = ∑ x, ν' x) : ν = ν' := by
  have hc := tvDist_vecMul_le_dobrushin_mul P h
  rw [hν, hν'] at hc
  have h0 : tvDist ν ν' = 0 := by
    nlinarith [tvDist_nonneg ν ν', dobrushin_nonneg P]
  exact (tvDist_eq_zero_iff ν ν').1 h0

end Contraction

section Powers

variable [DecidableEq Ω] [Nonempty Ω] {P : Matrix Ω Ω ℝ}

theorem dobrushin_pow_le (hP : P ∈ rowStochastic ℝ Ω) (t : ℕ) :
    dobrushin (P ^ t) ≤ dobrushin P ^ t := by
  induction t with
  | zero =>
    rw [_root_.pow_zero, _root_.pow_zero]
    exact dobrushin_le_one (isDistribution_row (one_mem (rowStochastic ℝ Ω)))
  | succ t ih =>
    rw [_root_.pow_succ, _root_.pow_succ]
    exact (dobrushin_mul_le (sum_row_of_mem_rowStochastic (pow_mem hP t)) P).trans
      (mul_le_mul_of_nonneg_right ih (dobrushin_nonneg P))

omit [Nonempty Ω] in
lemma vecMul_pow_eq_self {ν : Ω → ℝ} (hν : ν ᵥ* P = ν) (t : ℕ) : ν ᵥ* P ^ t = ν := by
  induction t with
  | zero => simp
  | succ t ih => rw [_root_.pow_succ, ← Matrix.vecMul_vecMul, ih, hν]

omit [Nonempty Ω] in
lemma isDistribution_single (x : Ω) : IsDistribution (Pi.single x 1 : Ω → ℝ) where
  nonneg y := by
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  sum_eq_one := by simp

/-- The distance of a row of `P ^ t` from a distribution stationary for `P` is at most
`dobrushin (P ^ t)`. -/
theorem tvDist_pow_row_le_dobrushin {ν : Ω → ℝ} (hν : IsDistribution ν) (hνP : ν ᵥ* P = ν)
    (t : ℕ) (x : Ω) : tvDist ((P ^ t) x) ν ≤ dobrushin (P ^ t) := by
  have hx := isDistribution_single x
  calc tvDist ((P ^ t) x) ν = tvDist (Pi.single x 1 ᵥ* P ^ t) (ν ᵥ* P ^ t) := by
        rw [single_one_vecMul, Matrix.row_apply', vecMul_pow_eq_self hνP]
    _ ≤ dobrushin (P ^ t) * tvDist (Pi.single x 1) ν :=
        tvDist_vecMul_le_dobrushin_mul _ (hx.sum_eq_one.trans hν.sum_eq_one.symm)
    _ ≤ dobrushin (P ^ t) * 1 :=
        mul_le_mul_of_nonneg_left (tvDist_le_one hx hν) (dobrushin_nonneg _)
    _ = dobrushin (P ^ t) := mul_one _

/-- **Convergence at the Dobrushin rate** from a start vector. -/
theorem tvDist_vecMul_pow_le (hP : P ∈ rowStochastic ℝ Ω) {μ ν : Ω → ℝ} (hνP : ν ᵥ* P = ν)
    (h : ∑ x, μ x = ∑ x, ν x) (t : ℕ) :
    tvDist (μ ᵥ* P ^ t) ν ≤ dobrushin P ^ t * tvDist μ ν :=
  calc tvDist (μ ᵥ* P ^ t) ν = tvDist (μ ᵥ* P ^ t) (ν ᵥ* P ^ t) := by
        rw [vecMul_pow_eq_self hνP]
    _ ≤ dobrushin (P ^ t) * tvDist μ ν := tvDist_vecMul_le_dobrushin_mul _ h
    _ ≤ dobrushin P ^ t * tvDist μ ν :=
        mul_le_mul_of_nonneg_right (dobrushin_pow_le hP t) (tvDist_nonneg _ _)

/-- **Convergence at the Dobrushin rate** from a start state. -/
theorem tvDist_pow_row_le_dobrushin_pow (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ}
    (hν : IsDistribution ν) (hνP : ν ᵥ* P = ν) (t : ℕ) (x : Ω) :
    tvDist ((P ^ t) x) ν ≤ dobrushin P ^ t :=
  (tvDist_pow_row_le_dobrushin hν hνP t x).trans (dobrushin_pow_le hP t)

/-- **Doeblin's theorem**: under the minorization `ε ν' ≤ P x` for a distribution `ν'`, every row
of `P ^ t` is within `(1 - ε) ^ t` of a stationary distribution. -/
theorem tvDist_pow_row_le_of_minorization (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ}
    (hν : IsDistribution ν) (hνP : ν ᵥ* P = ν) {ν' : Ω → ℝ} (hν' : IsDistribution ν')
    {ε : ℝ} (hm : ∀ x y, ε * ν' y ≤ P x y) (t : ℕ) (x : Ω) :
    tvDist ((P ^ t) x) ν ≤ (1 - ε) ^ t :=
  (tvDist_pow_row_le_dobrushin_pow hP hν hνP t x).trans
    (pow_le_pow_left₀ (dobrushin_nonneg P)
      (dobrushin_le_one_sub (isDistribution_row hP) hν' hm) t)

/-- The worst-case distance `d(t) = max_x tvDist ((P ^ t) x) ν` is at most `dobrushin (P ^ t)`. -/
theorem sup_tvDist_pow_row_le_dobrushin {ν : Ω → ℝ} (hν : IsDistribution ν) (hνP : ν ᵥ* P = ν)
    (t : ℕ) :
    Finset.univ.sup' Finset.univ_nonempty (fun x => tvDist ((P ^ t) x) ν) ≤ dobrushin (P ^ t) :=
  Finset.sup'_le _ _ fun x _ => tvDist_pow_row_le_dobrushin hν hνP t x

/-- `d(k t) ≤ (2 d(t)) ^ k` for the worst-case distance `d` to a stationary distribution. -/
theorem sup_tvDist_pow_row_mul_le (hP : P ∈ rowStochastic ℝ Ω) {ν : Ω → ℝ}
    (hν : IsDistribution ν) (hνP : ν ᵥ* P = ν) (t k : ℕ) :
    Finset.univ.sup' Finset.univ_nonempty (fun x => tvDist ((P ^ (t * k)) x) ν) ≤
      (2 * Finset.univ.sup' Finset.univ_nonempty fun x => tvDist ((P ^ t) x) ν) ^ k :=
  calc Finset.univ.sup' Finset.univ_nonempty (fun x => tvDist ((P ^ (t * k)) x) ν)
      ≤ dobrushin ((P ^ t) ^ k) := by
        rw [← _root_.pow_mul]
        exact sup_tvDist_pow_row_le_dobrushin hν hνP (t * k)
    _ ≤ dobrushin (P ^ t) ^ k := dobrushin_pow_le (pow_mem hP t) k
    _ ≤ _ := pow_le_pow_left₀ (dobrushin_nonneg _) (dobrushin_le_two_mul_sup _ ν) k

end Powers

end

end TheoremOS.Probability
