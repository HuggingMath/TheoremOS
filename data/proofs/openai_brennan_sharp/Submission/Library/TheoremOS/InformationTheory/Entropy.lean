import Mathlib

/-!
# Shannon entropy of finite distributions

Weights `p : ι → ℝ` on a finite type, entropy `H p = ∑ i, negMulLog (p i)` in nats, and the
relative entropy `D(p‖q) = ∑ i, p i * log (p i / q i)`. Contents: `0 ≤ H p ≤ log |ι|` for a
distribution, the uniform distribution attains `log |ι|`, Gibbs' inequality in an unnormalized
form, nonnegativity of relative entropy, the log-sum inequality, invariance under relabeling,
additivity on products, subadditivity of joint entropy, and monotonicity under pushforward.

Sources: T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
Chapter 2 (Theorem 2.6.3 information inequality, Theorem 2.6.4 `H ≤ log |𝒳|`, Theorem 2.6.6
independence bound, Theorem 2.7.1 log-sum inequality, Problem 2.4 entropy of a function).
Textbook material; nothing here is specific to a benchmark problem.

Bridges: a statement defining `entropy p := ∑ i, Real.negMulLog (p i)` is `entropy p` here by
`rfl`; `-(∑ i, p i * Real.log (p i))` is `entropy p` by `entropy_eq_neg_sum`; base-2 entropy is
`entropy p / Real.log 2`; `Real.binEntropy q` is the entropy of `![q, 1 - q]`-style weights on
`Bool` (`entropy_bool`).
-/

namespace TheoremOS.InformationTheory

open Finset Real
open scoped BigOperators

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Shannon entropy in nats. -/
def entropy (p : ι → ℝ) : ℝ := ∑ i, negMulLog (p i)

lemma entropy_eq_neg_sum (p : ι → ℝ) : entropy p = -∑ i, p i * log (p i) := by
  simp [entropy, negMulLog, Finset.sum_neg_distrib]

/-- Nonnegative weights summing to one. -/
structure IsDistribution (p : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ p i
  sum_eq_one : ∑ i, p i = 1

namespace IsDistribution

variable {p : ι → ℝ}

lemma le_one (hp : IsDistribution p) (i : ι) : p i ≤ 1 := by
  rw [← hp.sum_eq_one]
  exact Finset.single_le_sum (fun j _ => hp.nonneg j) (Finset.mem_univ i)

lemma nonempty (hp : IsDistribution p) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hp.sum_eq_one
  simp at this

end IsDistribution

/-- A pointwise form of `log x ≤ x - 1`: `a log b ≤ a log a + (b - a)` when `b = 0 → a = 0`. -/
lemma mul_log_le_mul_log_add_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b = 0 → a = 0) :
    a * log b ≤ a * log a + (b - a) := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb
  have hb' : 0 < b := lt_of_le_of_ne hb (fun h => ha.ne' (hab h.symm))
  have key := log_le_sub_one_of_pos (div_pos hb' ha)
  rw [log_div hb'.ne' ha.ne'] at key
  have h := mul_le_mul_of_nonneg_left key ha.le
  have e : a * (b / a - 1) = b - a := by field_simp
  nlinarith [h, e]

/-- **Gibbs' inequality**, unnormalized: for nonnegative weights with `∑ q ≤ ∑ p` and
`q i = 0 → p i = 0`, `∑ p log q ≤ ∑ p log p`. -/
theorem sum_mul_log_le_sum_mul_log {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpq : ∀ i, q i = 0 → p i = 0) (hsum : ∑ i, q i ≤ ∑ i, p i) :
    ∑ i, p i * log (q i) ≤ ∑ i, p i * log (p i) := by
  have h : ∑ i, p i * log (q i) ≤ ∑ i, (p i * log (p i) + (q i - p i)) :=
    Finset.sum_le_sum fun i _ => mul_log_le_mul_log_add_sub (hp i) (hq i) (hpq i)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at h
  linarith

/-- Gibbs' inequality for distributions: `H p ≤ -∑ p log q`. -/
theorem entropy_le_crossEntropy {p q : ι → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ i, q i = 0 → p i = 0) : entropy p ≤ -∑ i, p i * log (q i) := by
  rw [entropy_eq_neg_sum, neg_le_neg_iff]
  exact sum_mul_log_le_sum_mul_log hp.nonneg hq.nonneg hpq (by rw [hp.sum_eq_one, hq.sum_eq_one])

/-- Relative entropy (Kullback–Leibler divergence) in nats; terms with `p i = 0` vanish. -/
def relEntropy (p q : ι → ℝ) : ℝ := ∑ i, p i * log (p i / q i)

lemma relEntropy_eq_sub {p q : ι → ℝ} (hpq : ∀ i, q i = 0 → p i = 0) :
    relEntropy p q = ∑ i, p i * log (p i) - ∑ i, p i * log (q i) := by
  rw [relEntropy, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hp0 : p i = 0
  · simp [hp0]
  have hq0 : q i ≠ 0 := fun h => hp0 (hpq i h)
  rw [log_div hp0 hq0]
  ring

/-- **Information inequality**: `0 ≤ D(p‖q)` for distributions with `q i = 0 → p i = 0`. -/
theorem relEntropy_nonneg {p q : ι → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (hpq : ∀ i, q i = 0 → p i = 0) : 0 ≤ relEntropy p q := by
  rw [relEntropy_eq_sub hpq, sub_nonneg]
  exact sum_mul_log_le_sum_mul_log hp.nonneg hq.nonneg hpq (by rw [hp.sum_eq_one, hq.sum_eq_one])

theorem entropy_nonneg {p : ι → ℝ} (hp : IsDistribution p) : 0 ≤ entropy p :=
  Finset.sum_nonneg fun i _ => negMulLog_nonneg (hp.nonneg i) (hp.le_one i)

/-- The uniform weights `1 / |ι|`. -/
def uniform (ι : Type*) [Fintype ι] : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹

lemma isDistribution_uniform [Nonempty ι] : IsDistribution (uniform ι) where
  nonneg _ := by unfold uniform; positivity
  sum_eq_one := by
    have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [uniform, Finset.card_univ, this]

lemma entropy_uniform [Nonempty ι] : entropy (uniform ι) = log (Fintype.card ι) := by
  have : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [entropy, uniform, negMulLog, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, log_inv]
  field_simp

/-- `H p ≤ log |ι|`. -/
theorem entropy_le_log_card {p : ι → ℝ} (hp : IsDistribution p) :
    entropy p ≤ log (Fintype.card ι) := by
  have := hp.nonempty
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have h := entropy_le_crossEntropy hp isDistribution_uniform
    (fun i h => absurd h (inv_ne_zero hc.ne'))
  simp only [uniform, log_inv, mul_neg, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul,
    hp.sum_eq_one, one_mul] at h
  exact h

/-- Entropy does not depend on the labelling. -/
lemma entropy_comp_equiv (e : κ ≃ ι) (p : ι → ℝ) : entropy (p ∘ e) = entropy p := by
  simp only [entropy, Function.comp]
  exact e.sum_comp (fun i => negMulLog (p i))

/-- Weights on `Bool` with `p true = q`, `p false = 1 - q` have entropy `binEntropy q`. -/
lemma entropy_bool {p : Bool → ℝ} {q : ℝ} (htrue : p true = q) (hfalse : p false = 1 - q) :
    entropy p = binEntropy q := by
  rw [entropy, Fintype.sum_bool, htrue, hfalse, binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- **Additivity** on independent pairs: `H(p ⊗ q) = H p + H q`. -/
theorem entropy_prod {p : ι → ℝ} {q : κ → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    entropy (fun x : ι × κ => p x.1 * q x.2) = entropy p + entropy q := by
  simp only [entropy, negMulLog_mul, Fintype.sum_prod_type, Finset.sum_add_distrib]
  congr 1
  · simp only [← Finset.sum_mul, hq.sum_eq_one, one_mul]
  · rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hp.sum_eq_one, one_mul]

/-- The first marginal of weights on `ι × κ`. -/
def marginalLeft (r : ι × κ → ℝ) (i : ι) : ℝ := ∑ j, r (i, j)

/-- The second marginal of weights on `ι × κ`. -/
def marginalRight (r : ι × κ → ℝ) (j : κ) : ℝ := ∑ i, r (i, j)

lemma IsDistribution.marginalLeft {r : ι × κ → ℝ} (hr : IsDistribution r) :
    IsDistribution (marginalLeft r) where
  nonneg i := Finset.sum_nonneg fun j _ => hr.nonneg (i, j)
  sum_eq_one := by rw [← hr.sum_eq_one, Fintype.sum_prod_type]; rfl

lemma IsDistribution.marginalRight {r : ι × κ → ℝ} (hr : IsDistribution r) :
    IsDistribution (marginalRight r) where
  nonneg j := Finset.sum_nonneg fun i _ => hr.nonneg (i, j)
  sum_eq_one := by rw [← hr.sum_eq_one, Fintype.sum_prod_type_right]; rfl

omit [Fintype ι] in
lemma le_marginalLeft {r : ι × κ → ℝ} (hr : ∀ x, 0 ≤ r x) (x : ι × κ) : r x ≤ marginalLeft r x.1 :=
  Finset.single_le_sum (f := fun j => r (x.1, j)) (fun _ _ => hr _) (Finset.mem_univ x.2)

omit [Fintype κ] in
lemma le_marginalRight {r : ι × κ → ℝ} (hr : ∀ x, 0 ≤ r x) (x : ι × κ) : r x ≤ marginalRight r x.2 :=
  Finset.single_le_sum (f := fun i => r (i, x.2)) (fun _ _ => hr _) (Finset.mem_univ x.1)

/-- **Subadditivity** (independence bound): `H(X, Y) ≤ H X + H Y`. -/
theorem entropy_le_entropy_marginalLeft_add_marginalRight {r : ι × κ → ℝ} (hr : IsDistribution r) :
    entropy r ≤ entropy (marginalLeft r) + entropy (marginalRight r) := by
  have h1 := hr.marginalLeft
  have h2 := hr.marginalRight
  have hq : IsDistribution (fun x : ι × κ => marginalLeft r x.1 * marginalRight r x.2) :=
    ⟨fun x => mul_nonneg (h1.nonneg _) (h2.nonneg _), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, h2.sum_eq_one, mul_one, h1.sum_eq_one]⟩
  have hsupp : ∀ x : ι × κ, marginalLeft r x.1 * marginalRight r x.2 = 0 → r x = 0 := by
    intro x hx
    rcases mul_eq_zero.mp hx with h | h
    · exact le_antisymm (h ▸ le_marginalLeft hr.nonneg x) (hr.nonneg x)
    · exact le_antisymm (h ▸ le_marginalRight hr.nonneg x) (hr.nonneg x)
  have hlog : ∑ x : ι × κ, r x * log (marginalLeft r x.1 * marginalRight r x.2) =
      ∑ x : ι × κ, r x * log (marginalLeft r x.1) + ∑ x : ι × κ, r x * log (marginalRight r x.2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : r x = 0
    · simp [hx]
    have ha : marginalLeft r x.1 ≠ 0 := fun h => hx (hsupp x (by rw [h, zero_mul]))
    have hb : marginalRight r x.2 ≠ 0 := fun h => hx (hsupp x (by rw [h, mul_zero]))
    rw [log_mul ha hb, mul_add]
  have hleft : ∑ x : ι × κ, r x * log (marginalLeft r x.1) = -entropy (marginalLeft r) := by
    rw [entropy_eq_neg_sum, neg_neg, Fintype.sum_prod_type]
    simp only [marginalLeft, Finset.sum_mul]
  have hright : ∑ x : ι × κ, r x * log (marginalRight r x.2) = -entropy (marginalRight r) := by
    rw [entropy_eq_neg_sum, neg_neg, Fintype.sum_prod_type_right]
    simp only [marginalRight, Finset.sum_mul]
  have h := entropy_le_crossEntropy hr hq hsupp
  rw [hlog, hleft, hright] at h
  linarith

/-- `negMulLog` is subadditive on `[0, ∞)`. -/
lemma negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negMulLog (a + b) ≤ negMulLog a + negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp
  have h1 : log a ≤ log (a + b) := log_le_log ha' (by linarith)
  have h2 : b * log b ≤ b * log (a + b) := by
    rcases hb.eq_or_lt with rfl | hb'
    · simp
    exact mul_le_mul_of_nonneg_left (log_le_log hb' (by linarith)) hb
  simp only [negMulLog]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha]

lemma negMulLog_sum_le {α : Type*} (s : Finset α) {f : α → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negMulLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    calc negMulLog (f a + ∑ i ∈ s, f i)
        ≤ negMulLog (f a) + negMulLog (∑ i ∈ s, f i) :=
          negMulLog_add_le (hf a (Finset.mem_insert_self a s)) (Finset.sum_nonneg hs)
      _ ≤ negMulLog (f a) + ∑ i ∈ s, negMulLog (f i) := by linarith [ih hs]

/-- The pushforward of weights along `f`. -/
def pushforward [DecidableEq κ] (f : ι → κ) (p : ι → ℝ) (j : κ) : ℝ := ∑ i with f i = j, p i

lemma IsDistribution.pushforward [DecidableEq κ] {p : ι → ℝ} (hp : IsDistribution p) (f : ι → κ) :
    IsDistribution (pushforward f p) :=
  ⟨fun _ => Finset.sum_nonneg fun i _ => hp.nonneg i, by
    rw [← hp.sum_eq_one]; exact Finset.sum_fiberwise Finset.univ f p⟩

/-- **Entropy of a function**: `H(f(X)) ≤ H(X)`. -/
theorem entropy_pushforward_le [DecidableEq κ] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (f : ι → κ) :
    entropy (pushforward f p) ≤ entropy p := by
  calc entropy (pushforward f p) = ∑ j, negMulLog (∑ i with f i = j, p i) := rfl
    _ ≤ ∑ j, ∑ i with f i = j, negMulLog (p i) :=
        Finset.sum_le_sum fun j _ => negMulLog_sum_le _ fun i _ => hp i
    _ = entropy p := Finset.sum_fiberwise Finset.univ f (fun i => negMulLog (p i))

/-- **Log-sum inequality**: `(∑ a) log (∑ a / ∑ b) ≤ ∑ a log (a / b)` for nonnegative weights with
`b i = 0 → a i = 0`. -/
theorem sum_mul_log_div_le {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hab : ∀ i, b i = 0 → a i = 0) :
    (∑ i, a i) * log ((∑ i, a i) / ∑ i, b i) ≤ ∑ i, a i * log (a i / b i) := by
  set A := ∑ i, a i with hA
  set B := ∑ i, b i with hB
  have hterm : ∀ i, a i * log (a i / b i) = a i * log (a i) - a i * log (b i) := by
    intro i
    by_cases h0 : a i = 0
    · simp [h0]
    rw [log_div h0 (fun h => h0 (hab i h))]
    ring
  rcases (show 0 ≤ A from Finset.sum_nonneg fun i _ => ha i).eq_or_lt with hA0 | hA0
  · rw [← hA0, zero_mul]
    have hA0' : ∑ i, a i = 0 := by rw [← hA]; exact hA0.symm
    have hz : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => ha j).mp hA0' i (Finset.mem_univ i)
    simp [hz]
  have hB0 : 0 < B := by
    refine (Finset.sum_nonneg fun i _ => hb i).lt_of_ne fun h => hA0.ne' ?_
    have hz : ∀ i, b i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hb j).mp h.symm i (Finset.mem_univ i)
    exact Finset.sum_eq_zero fun i _ => hab i (hz i)
  set c := A / B with hc
  have hc0 : 0 < c := div_pos hA0 hB0
  have hgibbs := sum_mul_log_le_sum_mul_log ha (fun i => mul_nonneg (hb i) hc0.le)
    (fun i h => hab i ((mul_eq_zero.mp h).resolve_right hc0.ne'))
    (le_of_eq (by rw [← Finset.sum_mul, ← hB, ← hA, hc]; field_simp))
  have hsplit : ∑ i, a i * log (b i * c) = ∑ i, a i * log (b i) + A * log c := by
    rw [hA, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : a i = 0
    · simp [h0]
    rw [log_mul (fun h => h0 (hab i h)) hc0.ne', mul_add]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib]
  linarith

end

end TheoremOS.InformationTheory
