import Submission.Library.TheoremOS.Probability.SpectralGap

/-!
# Lower bounds for mixing

Tools that show a finite Markov chain has *not* mixed yet. Contents: the test-function bound
`|E_μ f - E_ν f| ≤ 2 M tvDist μ ν` for `|f| ≤ M`; **eigenfunction bounds**: for `P f = θ f`
with `θ ≠ 1` and a stationary `π`, `E_π f = 0` and `|θ|^t |f x| ≤ 2 ‖f‖∞ tvDist (P^t x) π`,
so rows within `ε` of `π` force `|θ|^t ≤ 2ε` and `t ≥ log (1/(2ε)) / log (1/|θ|)`; the
**edge flow** `Q(S, T) = ∑_{x ∈ S, y ∈ T} π x P x y` and the **bottleneck ratio**
`Φ(S) = Q(S, Sᶜ) / π(S)`; for reversible chains the Dirichlet form of `1_S` is `Q(S, Sᶜ)` and
its variance is `π(S) π(Sᶜ)`, giving the easy half of **Cheeger's inequality**
`γ π(S) π(Sᶜ) ≤ Q(S, Sᶜ)` and `γ ≤ 2 Φ(S)` when `π(S) ≤ 1/2`; the **bottleneck lower bound**:
some `x ∈ S` has `tvDist (P^t x) π ≥ π(Sᶜ) - t Φ(S)`, hence rows within `1/4` at time `t`
force `1 ≤ 4 t Φ(S)`; convexity `tvDist (μ K) ν ≤ ∑ μ x tvDist (K x) ν`; and **Wilson's
distinguishing statistic**: if `E_μ f - E_ν f ≥ r σ` and both variances are at most `σ²`, then
`tvDist μ ν ≥ 1 - 8 / r²`.

Sources: D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS, 2017,
Sections 7.1–7.3, 12.2 and 13.3 (Theorem 7.4, Proposition 7.9, Theorem 12.5, Theorem 13.10);
D. B. Wilson, Mixing times of lozenge tiling and card shuffling Markov chains, Ann. Appl.
Probab. 14 (2004). Textbook material; nothing here is specific to a benchmark problem.

Bridges: `P` is a `Matrix Ω Ω ℝ` with `P ∈ rowStochastic ℝ Ω`, a stationary law is `π ᵥ* P = π`,
and a reversible one satisfies `hrev : ∀ x y, π x * P x y = π y * P y x`. Events are
`Finset Ω`; `prob π S` is `∑ x ∈ S, π x`, and `condLaw π S` is `π` conditioned on `S`.
-/

namespace TheoremOS.Probability

open Finset Matrix
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [Fintype Ω]

section TestFunctions

/-- A function bounded by `M` separates two weight vectors by at most `2 M tvDist`. -/
theorem abs_expectation_sub_le {μ ν f : Ω → ℝ} {M : ℝ} (hf : ∀ ω, |f ω| ≤ M) :
    |expectation μ f - expectation ν f| ≤ 2 * M * tvDist μ ν := by
  have h : expectation μ f - expectation ν f = ∑ ω, (μ ω - ν ω) * f ω := by
    simp only [expectation, sub_mul, Finset.sum_sub_distrib]
  rw [h]
  calc |∑ ω, (μ ω - ν ω) * f ω| ≤ ∑ ω, |μ ω - ν ω| * M :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hf ω) (abs_nonneg _))
    _ = 2 * M * tvDist μ ν := by
        rw [tvDist, ← Finset.sum_mul]
        ring

end TestFunctions

section Eigen

variable [DecidableEq Ω] {P : Matrix Ω Ω ℝ} {f : Ω → ℝ} {θ : ℝ}

lemma pow_mulVec_of_eigen (hf : P *ᵥ f = θ • f) (t : ℕ) : P ^ t *ᵥ f = θ ^ t • f := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [_root_.pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hf, smul_smul,
      ← _root_.pow_succ]

omit [DecidableEq Ω] in
/-- Stationary expectations of an eigenfunction with eigenvalue `θ ≠ 1` vanish. -/
lemma expectation_eq_zero_of_eigen {π : Ω → ℝ} (hπP : π ᵥ* P = π) (hf : P *ᵥ f = θ • f)
    (hθ : θ ≠ 1) : expectation π f = 0 := by
  have h : expectation π (P *ᵥ f) = expectation π f := by
    change π ⬝ᵥ (P *ᵥ f) = π ⬝ᵥ f
    rw [Matrix.dotProduct_mulVec, hπP]
  have h' : expectation π (θ • f) = θ * expectation π f := by
    simp only [expectation, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [hf, h'] at h
  have : (θ - 1) * expectation π f = 0 := by linarith
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hθ)

/-- The **eigenfunction lower bound**: `|θ|^t |f x| ≤ 2 ‖f‖∞ tvDist (P^t x) π`. -/
theorem pow_abs_mul_le_tvDist {π : Ω → ℝ} (hπP : π ᵥ* P = π) (hf : P *ᵥ f = θ • f)
    (hθ : θ ≠ 1) {M : ℝ} (hM : ∀ ω, |f ω| ≤ M) (t : ℕ) (x : Ω) :
    |θ| ^ t * |f x| ≤ 2 * M * tvDist ((P ^ t) x) π := by
  have h1 : expectation ((P ^ t) x) f = θ ^ t * f x := by
    change (P ^ t *ᵥ f) x = _
    rw [pow_mulVec_of_eigen hf t, Pi.smul_apply, smul_eq_mul]
  have h2 := abs_expectation_sub_le (μ := (P ^ t) x) (ν := π) hM
  rw [h1, expectation_eq_zero_of_eigen hπP hf hθ, sub_zero, abs_mul, abs_pow] at h2
  exact h2

/-- If every row is within `ε` of `π` at time `t`, a nonzero eigenfunction with eigenvalue
`θ ≠ 1` has `|θ|^t ≤ 2 ε`. -/
theorem pow_abs_le_two_mul_of_eigen {π : Ω → ℝ} (hπP : π ᵥ* P = π) (hf : P *ᵥ f = θ • f)
    (hθ : θ ≠ 1) (hf0 : f ≠ 0) {t : ℕ} {ε : ℝ} (ht : ∀ x, tvDist ((P ^ t) x) π ≤ ε) :
    |θ| ^ t ≤ 2 * ε := by
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    exact hf0 (funext fun y => not_not.1 fun hy => h ⟨y, hy⟩)
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ (fun ω => |f ω|) ⟨y, mem_univ y⟩
  have hM : ∀ ω, |f ω| ≤ |f x| := fun ω => hx ω (mem_univ ω)
  have hpos : 0 < |f x| := (abs_pos.2 hy).trans_le (hM y)
  have h1 := pow_abs_mul_le_tvDist hπP hf hθ hM t x
  have h2 : 2 * |f x| * tvDist ((P ^ t) x) π ≤ 2 * |f x| * ε :=
    mul_le_mul_of_nonneg_left (ht x) (by positivity)
  have h3 : |θ| ^ t * |f x| ≤ 2 * ε * |f x| := by linarith
  exact le_of_mul_le_mul_right h3 hpos

/-- **Relaxation lower bound on mixing**: rows within `ε` of `π` at time `t` force
`t log (1/|θ|) ≥ log (1/(2ε))` for every nonzero eigenfunction with eigenvalue `θ ∉ {0, 1}`. -/
theorem log_le_mul_log_of_eigen {π : Ω → ℝ} (hπP : π ᵥ* P = π) (hf : P *ᵥ f = θ • f)
    (hθ : θ ≠ 1) (hθ0 : θ ≠ 0) (hf0 : f ≠ 0) {t : ℕ} {ε : ℝ}
    (ht : ∀ x, tvDist ((P ^ t) x) π ≤ ε) :
    Real.log (1 / (2 * ε)) ≤ t * Real.log (1 / |θ|) := by
  have h := pow_abs_le_two_mul_of_eigen hπP hf hθ hf0 ht
  have hpos : 0 < |θ| ^ t := pow_pos (abs_pos.2 hθ0) t
  have hl := Real.log_le_log hpos h
  rw [Real.log_pow] at hl
  rw [one_div, one_div, Real.log_inv, Real.log_inv, mul_neg]
  linarith

end Eigen

section Bottleneck

variable {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}

/-- The **edge flow** `Q(S, T) = ∑_{x ∈ S, y ∈ T} π x P x y`. -/
def edgeFlow (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) (S T : Finset Ω) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ T, π x * P x y

omit [Fintype Ω] in
lemma edgeFlow_nonneg (hπ : ∀ x, 0 ≤ π x) (hP : ∀ x y, 0 ≤ P x y) (S T : Finset Ω) :
    0 ≤ edgeFlow π P S T :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hπ x) (hP x y)

omit [Fintype Ω] in
/-- Reversibility makes the edge flow symmetric. -/
lemma edgeFlow_comm (hrev : ∀ x y, π x * P x y = π y * P y x) (S T : Finset Ω) :
    edgeFlow π P S T = edgeFlow π P T S := by
  rw [edgeFlow, edgeFlow, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => hrev x y

variable [DecidableEq Ω]

/-- The **bottleneck ratio** `Φ(S) = Q(S, Sᶜ) / π(S)`. -/
def bottleneckRatio (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) (S : Finset Ω) : ℝ :=
  edgeFlow π P S Sᶜ / prob π S

lemma bottleneckRatio_nonneg (hπ : ∀ x, 0 ≤ π x) (hP : ∀ x y, 0 ≤ P x y) (S : Finset Ω) :
    0 ≤ bottleneckRatio π P S :=
  div_nonneg (edgeFlow_nonneg hπ hP S Sᶜ) (prob_nonneg hπ S)

/-- The variance of an indicator is `π(S) π(Sᶜ)`. -/
lemma variance_indicator (hπ : IsDistribution π) (S : Finset Ω) :
    variance π (fun x => if x ∈ S then 1 else 0) = prob π S * prob π Sᶜ := by
  have h1 := prob_eq_expectation_indicator π S
  have h2 : expectation π (fun x => (if x ∈ S then (1 : ℝ) else 0) ^ 2) = prob π S := by
    rw [h1]
    exact Finset.sum_congr rfl fun ω _ => by by_cases hω : ω ∈ S <;> simp [hω]
  rw [variance_eq hπ, h2, ← h1, prob_compl hπ]
  ring

/-- For a reversible chain the Dirichlet form of `1_S` is the edge flow `Q(S, Sᶜ)`. -/
theorem dirichletForm_indicator (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (S : Finset Ω) :
    dirichletForm π P (fun x => if x ∈ S then 1 else 0) = edgeFlow π P S Sᶜ := by
  have h := two_mul_dirichletForm hrow hrev (fun x => if x ∈ S then (1 : ℝ) else 0)
  have hsq : ∀ x y, π x * P x y * ((if x ∈ S then (1 : ℝ) else 0) - if y ∈ S then 1 else 0) ^ 2
      = (if x ∈ S then (if y ∈ Sᶜ then π x * P x y else 0) else 0)
        + (if y ∈ S then (if x ∈ Sᶜ then π y * P y x else 0) else 0) := fun x y => by
    by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;> simp [hx, hy, hrev x y]
  have hA : ∑ x, ∑ y, (if x ∈ S then (if y ∈ Sᶜ then π x * P x y else 0) else 0)
      = edgeFlow π P S Sᶜ := by
    rw [edgeFlow, ← Fintype.sum_ite_mem S]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceIte]
      exact Fintype.sum_ite_mem _ _
    · simp [hx]
  have hB : ∑ x, ∑ y, (if y ∈ S then (if x ∈ Sᶜ then π y * P y x else 0) else 0)
      = edgeFlow π P S Sᶜ := by
    rw [Finset.sum_comm]
    exact hA
  simp only [hsq, Finset.sum_add_distrib, hA, hB] at h
  linarith

/-- The easy half of **Cheeger's inequality**: a spectral gap `γ` of a reversible chain gives
`γ π(S) π(Sᶜ) ≤ Q(S, Sᶜ)`. -/
theorem HasSpectralGap.mul_prob_mul_prob_le {γ : ℝ} (hγ : HasSpectralGap π P γ)
    (hπ : IsDistribution π) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (S : Finset Ω) :
    γ * (prob π S * prob π Sᶜ) ≤ edgeFlow π P S Sᶜ := by
  have h := hγ fun x => if x ∈ S then 1 else 0
  rwa [variance_indicator hπ S, dirichletForm_indicator hrow hrev S] at h

/-- A spectral gap is at most twice the bottleneck ratio of any `S` with `0 < π(S) ≤ 1/2`. -/
theorem HasSpectralGap.le_two_mul_bottleneckRatio {γ : ℝ} (hγ : HasSpectralGap π P γ)
    (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) {S : Finset Ω} (hS : 0 < prob π S)
    (hS2 : prob π S ≤ 1 / 2) : γ ≤ 2 * bottleneckRatio π P S := by
  have h := hγ.mul_prob_mul_prob_le hπ hrow hrev S
  rw [prob_compl hπ] at h
  have hQ := edgeFlow_nonneg hπ.nonneg hP S Sᶜ
  have key : γ * prob π S ≤ 2 * edgeFlow π P S Sᶜ := by
    rcases le_or_gt 0 γ with hγ0 | hγ0
    · nlinarith [mul_nonneg (mul_nonneg hγ0 hS.le) (sub_nonneg.2 hS2)]
    · nlinarith [mul_neg_of_neg_of_pos hγ0 hS]
  rw [bottleneckRatio, mul_div_assoc', le_div_iff₀ hS]
  exact key

/-- `π` conditioned on `S`. -/
def condLaw (π : Ω → ℝ) (S : Finset Ω) (x : Ω) : ℝ := if x ∈ S then π x / prob π S else 0

lemma isDistribution_condLaw (hπ : ∀ x, 0 ≤ π x) {S : Finset Ω} (hS : 0 < prob π S) :
    IsDistribution (condLaw π S) where
  nonneg x := by
    unfold condLaw
    split_ifs
    · exact div_nonneg (hπ x) hS.le
    · exact le_rfl
  sum_eq_one := by
    simp only [condLaw]
    rw [Fintype.sum_ite_mem, ← Finset.sum_div]
    exact div_self hS.ne'

lemma prob_condLaw_compl (S : Finset Ω) : prob (condLaw π S) Sᶜ = 0 :=
  Finset.sum_eq_zero fun x hx => by simp [condLaw, Finset.mem_compl.1 hx]

lemma prob_compl_le_tvDist_condLaw (hπ : IsDistribution π) {S : Finset Ω}
    (hS : 0 < prob π S) : prob π Sᶜ ≤ tvDist π (condLaw π S) := by
  have h := prob_sub_prob_le_tvDist
    (hπ.sum_eq_one.trans (isDistribution_condLaw hπ.nonneg hS).sum_eq_one.symm) Sᶜ
  rwa [prob_condLaw_compl, sub_zero] at h

lemma vecMul_condLaw_apply (S : Finset Ω) (y : Ω) :
    (condLaw π S ᵥ* P) y = (∑ x ∈ S, π x * P x y) / prob π S := by
  simp only [Matrix.vecMul, dotProduct, condLaw, ite_mul, zero_mul]
  rw [Fintype.sum_ite_mem, Finset.sum_div]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- One step from `π` conditioned on `S` moves it by at most the bottleneck ratio. -/
theorem tvDist_vecMul_condLaw_le (hπ : ∀ x, 0 ≤ π x) (hP : P ∈ rowStochastic ℝ Ω)
    (hπP : π ᵥ* P = π) {S : Finset Ω} (hS : 0 < prob π S) :
    tvDist (condLaw π S ᵥ* P) (condLaw π S) ≤ bottleneckRatio π P S := by
  have hμ := isDistribution_condLaw hπ hS
  rw [tvDist_eq_sum_max ((isDistribution_vecMul hP hμ).sum_eq_one.trans hμ.sum_eq_one.symm)]
  have hterm : ∀ y, max ((condLaw π S ᵥ* P) y - condLaw π S y) 0 ≤
      if y ∈ Sᶜ then (∑ x ∈ S, π x * P x y) / prob π S else 0 := fun y => by
    rw [vecMul_condLaw_apply]
    by_cases hy : y ∈ S
    · have hle : ∑ x ∈ S, π x * P x y ≤ π y := by
        calc ∑ x ∈ S, π x * P x y ≤ ∑ x, π x * P x y :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
                fun x _ _ => mul_nonneg (hπ x) (nonneg_of_mem_rowStochastic hP)
          _ = π y := congrFun hπP y
      have h2 : (∑ x ∈ S, π x * P x y) / prob π S - condLaw π S y ≤ 0 := by
        simp only [condLaw, hy, ↓reduceIte]
        exact sub_nonpos.2 (div_le_div_of_nonneg_right hle hS.le)
      rw [max_eq_right h2]
      simp [hy]
    · have hy' : y ∈ Sᶜ := Finset.mem_compl.2 hy
      simp only [condLaw, hy, hy', ↓reduceIte, sub_zero]
      exact max_le le_rfl (div_nonneg (Finset.sum_nonneg fun x _ =>
        mul_nonneg (hπ x) (nonneg_of_mem_rowStochastic hP)) hS.le)
  refine (Finset.sum_le_sum fun y _ => hterm y).trans_eq ?_
  rw [Fintype.sum_ite_mem, bottleneckRatio, edgeFlow, ← Finset.sum_div, Finset.sum_comm]

/-- `t` steps from `π` conditioned on `S` move it by at most `t Φ(S)`. -/
theorem tvDist_vecMul_pow_condLaw_le (hπ : ∀ x, 0 ≤ π x) (hP : P ∈ rowStochastic ℝ Ω)
    (hπP : π ᵥ* P = π) {S : Finset Ω} (hS : 0 < prob π S) (t : ℕ) :
    tvDist (condLaw π S ᵥ* P ^ t) (condLaw π S) ≤ t * bottleneckRatio π P S := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 := tvDist_triangle (condLaw π S ᵥ* P ^ (t + 1)) (condLaw π S ᵥ* P ^ t)
      (condLaw π S)
    have h2 : tvDist (condLaw π S ᵥ* P ^ (t + 1)) (condLaw π S ᵥ* P ^ t) ≤
        bottleneckRatio π P S := by
      rw [_root_.pow_succ', ← Matrix.vecMul_vecMul]
      exact (tvDist_vecMul_le (pow_mem hP t) _ _).trans (tvDist_vecMul_condLaw_le hπ hP hπP hS)
    rw [Nat.cast_succ, add_mul, one_mul]
    linarith

omit [DecidableEq Ω] in
/-- Total variation to a fixed law is convex in the starting law: for a distribution `μ`,
`tvDist (μ K) ν ≤ ∑ μ x tvDist (K x) ν`. -/
theorem tvDist_vecMul_le_sum {μ : Ω → ℝ} (hμ : IsDistribution μ) (K : Matrix Ω Ω ℝ)
    (ν : Ω → ℝ) : tvDist (μ ᵥ* K) ν ≤ ∑ x, μ x * tvDist (K x) ν := by
  have h : ∀ y, (μ ᵥ* K) y - ν y = ∑ x, μ x * (K x y - ν y) := fun y => by
    change ∑ x, μ x * K x y - ν y = _
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ.sum_eq_one, one_mul]
  calc tvDist (μ ᵥ* K) ν = (1 / 2 : ℝ) * ∑ y, |∑ x, μ x * (K x y - ν y)| := by
        simp only [tvDist, h]
    _ ≤ (1 / 2 : ℝ) * ∑ y, ∑ x, |μ x * (K x y - ν y)| :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun y _ => Finset.abs_sum_le_sum_abs _ _) (by norm_num)
    _ = ∑ x, μ x * tvDist (K x) ν := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [abs_mul, abs_of_nonneg (hμ.nonneg x), tvDist, ← Finset.mul_sum]
        ring

/-- The **bottleneck lower bound**: some `x ∈ S` has `tvDist (P^t x) π ≥ π(Sᶜ) - t Φ(S)`. -/
theorem exists_mem_le_tvDist_pow_row (hπ : IsDistribution π) (hP : P ∈ rowStochastic ℝ Ω)
    (hπP : π ᵥ* P = π) {S : Finset Ω} (hS : 0 < prob π S) (t : ℕ) :
    ∃ x ∈ S, prob π Sᶜ - t * bottleneckRatio π P S ≤ tvDist ((P ^ t) x) π := by
  have hμ := isDistribution_condLaw hπ.nonneg hS
  have h1 := prob_compl_le_tvDist_condLaw hπ hS
  have h2 := tvDist_vecMul_pow_condLaw_le hπ.nonneg hP hπP hS t
  have h3 := tvDist_triangle π (condLaw π S ᵥ* P ^ t) (condLaw π S)
  have h4 := tvDist_vecMul_le_sum hμ (P ^ t) π
  have hne : S.Nonempty := Finset.nonempty_of_sum_ne_zero hS.ne'
  obtain ⟨x, hxS, hx⟩ := Finset.exists_max_image S (fun z => tvDist ((P ^ t) z) π) hne
  have h5 : ∑ z, condLaw π S z * tvDist ((P ^ t) z) π ≤ tvDist ((P ^ t) x) π := by
    calc ∑ z, condLaw π S z * tvDist ((P ^ t) z) π
        ≤ ∑ z, condLaw π S z * tvDist ((P ^ t) x) π := Finset.sum_le_sum fun z _ => by
          by_cases hz : z ∈ S
          · exact mul_le_mul_of_nonneg_left (hx z hz) (hμ.nonneg z)
          · simp [condLaw, hz]
      _ = tvDist ((P ^ t) x) π := by rw [← Finset.sum_mul, hμ.sum_eq_one, one_mul]
  refine ⟨x, hxS, ?_⟩
  rw [tvDist_comm π (condLaw π S ᵥ* P ^ t)] at h3
  linarith

/-- If every row is within `ε` of `π` at time `t`, then `π(Sᶜ) - ε ≤ t Φ(S)` for each `S`
with `π(S) > 0`. -/
theorem prob_compl_sub_le_mul_bottleneckRatio (hπ : IsDistribution π)
    (hP : P ∈ rowStochastic ℝ Ω) (hπP : π ᵥ* P = π) {S : Finset Ω} (hS : 0 < prob π S)
    {t : ℕ} {ε : ℝ} (ht : ∀ x, tvDist ((P ^ t) x) π ≤ ε) :
    prob π Sᶜ - ε ≤ t * bottleneckRatio π P S := by
  obtain ⟨x, -, hx⟩ := exists_mem_le_tvDist_pow_row hπ hP hπP hS t
  linarith [ht x]

/-- Rows within `1/4` of `π` at time `t` force `1 ≤ 4 t Φ(S)` whenever `0 < π(S) ≤ 1/2`. -/
theorem one_le_four_mul_bottleneckRatio (hπ : IsDistribution π) (hP : P ∈ rowStochastic ℝ Ω)
    (hπP : π ᵥ* P = π) {S : Finset Ω} (hS : 0 < prob π S) (hS2 : prob π S ≤ 1 / 2) {t : ℕ}
    (ht : ∀ x, tvDist ((P ^ t) x) π ≤ 1 / 4) : 1 ≤ 4 * (t * bottleneckRatio π P S) := by
  have h := prob_compl_sub_le_mul_bottleneckRatio hπ hP hπP hS ht
  rw [prob_compl hπ] at h
  linarith

end Bottleneck

section Wilson

/-- **Wilson's distinguishing statistic**: if `E_μ f - E_ν f ≥ r σ` and both variances are at
most `σ²`, then `tvDist μ ν ≥ 1 - 8 / r²`. -/
theorem one_sub_le_tvDist_of_expectation_sub {μ ν : Ω → ℝ} (hμ : IsDistribution μ)
    (hν : IsDistribution ν) (f : Ω → ℝ) {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ)
    (hgap : r * σ ≤ expectation μ f - expectation ν f) (hvμ : variance μ f ≤ σ ^ 2)
    (hvν : variance ν f ≤ σ ^ 2) : 1 - 8 / r ^ 2 ≤ tvDist μ ν := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, expectation μ f - expectation ν f = 2 * d := ⟨_, (mul_div_cancel₀ _
    (two_ne_zero (α := ℝ))).symm⟩
  have hd0 : r * σ / 2 ≤ d := by linarith
  have hdpos : 0 < d := lt_of_lt_of_le (by positivity) hd0
  have hratio : σ ^ 2 / d ^ 2 ≤ 4 / r ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul hd0 hd0 (by positivity) hdpos.le]
  have hvar : ∀ {p : Ω → ℝ}, variance p f ≤ σ ^ 2 → variance p f / d ^ 2 ≤ 4 / r ^ 2 :=
    fun h => (div_le_div_of_nonneg_right h (by positivity)).trans hratio
  let A : Finset Ω := {ω | expectation ν f + d ≤ f ω}
  have hAc : prob μ Aᶜ ≤ 4 / r ^ 2 := by
    refine (prob_mono hμ.nonneg ?_).trans ((chebyshev hμ f hdpos).trans (hvar hvμ))
    intro ω hω
    simp only [A, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_le] at hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [abs_sub_comm]
    exact (by linarith : d ≤ expectation μ f - f ω).trans (le_abs_self _)
  have hA : prob ν A ≤ 4 / r ^ 2 := by
    refine (prob_mono hν.nonneg ?_).trans ((chebyshev hν f hdpos).trans (hvar hvν))
    intro ω hω
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (by linarith : d ≤ f ω - expectation ν f).trans (le_abs_self _)
  have hT := prob_sub_prob_le_tvDist (hμ.sum_eq_one.trans hν.sum_eq_one.symm) A
  rw [prob_compl hμ] at hAc
  have h8 : 8 / r ^ 2 = 4 / r ^ 2 + 4 / r ^ 2 := by ring
  linarith

end Wilson

end

end TheoremOS.Probability
