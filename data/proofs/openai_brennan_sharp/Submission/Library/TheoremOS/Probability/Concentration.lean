import Submission.Library.TheoremOS.Probability.BiasedProduct

/-!
# Chernoff and Hoeffding bounds for the `p`-biased product measure

Tail bounds for a random subset `s` of the finite type `α` drawn from `biasedMass p`, stated as
finite sums. Contents: the exponential Markov (Chernoff) bound for any nonnegative weights and
its sub-Gaussian corollary; Hoeffding's lemma for one Bernoulli coordinate,
`p e^{s(1-p)} + (1-p) e^{-sp} ≤ e^{s²/8}` (from Mathlib's measure-theoretic Hoeffding lemma); the
exponential moment of a weighted count `∑ x, d x (1[x ∈ s] - p)`; Hoeffding's inequality for
weighted counts, upper, lower and two-sided, `P(|∑ x, d x (1[x ∈ s] - p)| ≥ u) ≤
2 exp(-2u²/∑ d²)`; the same for `|s|` against `p |α|`; the relative-entropy Chernoff bounds
`P(|s| ≥ a n) ≤ exp(-n D(a‖p))` for `p ≤ a < 1` and `P(|s| ≤ a n) ≤ exp(-n D(a‖p))` for
`0 < a ≤ p`; the multiplicative bound `P(|s| ≥ (1+δ) p n) ≤ exp(-p n ((1+δ) log(1+δ) - δ))`; and
the counting form for `p = 1/2`.

Sources: N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, Appendix A;
M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed., Cambridge University Press,
2017, Sections 4.2–4.5; W. Hoeffding, Probability inequalities for sums of bounded random
variables, J. Amer. Statist. Assoc. 58 (1963). Textbook material; nothing here is specific to a
benchmark problem.

Bridges: a probability `∑ s ∈ D, biasedMass p s` with `D` a filter on the size or a weighted count
is the left side of the theorems here. For a configuration measure use `sum_biasedWeight_mul` and
`card_filter_configOf` to move to subsets. `klBernoulli a p` is `relEntropy` of the two-point
laws (`klBernoulli_eq_relEntropy`). With `n = Fintype.card α` and `p = 1/2`,
`card_filter_card_ge_le` counts subsets of size `≥ n/2 + u`.
-/

namespace TheoremOS.Probability

open Finset Real
open TheoremOS.InformationTheory

noncomputable section

section Chernoff

variable {ι : Type*} [Fintype ι]

/-- Exponential Markov: `∑_{c ≤ Y i} w i ≤ e^{-tc} ∑ w i e^{t Y i}` for `t ≥ 0`. -/
theorem sum_filter_le_exp_mul_sum (w Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {t : ℝ} (ht : 0 ≤ t)
    (c : ℝ) :
    ∑ i with c ≤ Y i, w i ≤ exp (-(t * c)) * ∑ i, w i * exp (t * Y i) := by
  calc ∑ i with c ≤ Y i, w i
      ≤ ∑ i with c ≤ Y i, w i * exp (t * (Y i - c)) :=
        Finset.sum_le_sum fun i hi => by
          have h := (Finset.mem_filter.mp hi).2
          exact le_mul_of_one_le_right (hw i) (one_le_exp (mul_nonneg ht (by linarith)))
    _ ≤ ∑ i, w i * exp (t * (Y i - c)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun i _ _ =>
          mul_nonneg (hw i) (exp_pos _).le
    _ = exp (-(t * c)) * ∑ i, w i * exp (t * Y i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show t * (Y i - c) = t * Y i + -(t * c) by ring, exp_add]
        ring

/-- A sub-Gaussian exponential moment gives a Gaussian tail. -/
theorem sum_filter_le_of_subgaussian (w Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {c : ℝ} (hc : 0 < c)
    (hY : ∀ t, 0 ≤ t → ∑ i, w i * exp (t * Y i) ≤ exp (c * t ^ 2 / 2)) {u : ℝ} (hu : 0 ≤ u) :
    ∑ i with u ≤ Y i, w i ≤ exp (-(u ^ 2 / (2 * c))) := by
  have ht : 0 ≤ u / c := div_nonneg hu hc.le
  calc ∑ i with u ≤ Y i, w i ≤ exp (-(u / c * u)) * ∑ i, w i * exp (u / c * Y i) :=
        sum_filter_le_exp_mul_sum w Y hw ht u
    _ ≤ exp (-(u / c * u)) * exp (c * (u / c) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (hY _ ht) (exp_pos _).le
    _ = exp (-(u ^ 2 / (2 * c))) := by
        rw [← exp_add]
        congr 1
        field_simp
        ring

end Chernoff

/-- Hoeffding's lemma for one centred Bernoulli coordinate. -/
theorem bernoulli_exp_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) :
    p * exp (s * (1 - p)) + (1 - p) * exp (-(s * p)) ≤ exp (s ^ 2 / 8) := by
  obtain ⟨q, rfl⟩ : ∃ q : unitInterval, (q : ℝ) = p := ⟨⟨p, hp₀, hp₁⟩, rfl⟩
  let X : Bool → ℝ := fun b => if b then 1 - (q : ℝ) else -(q : ℝ)
  have hb : ∀ᵐ b ∂(ProbabilityTheory.bernoulliMeasure true false q),
      X b ∈ Set.Icc (-(q : ℝ)) (1 - q) :=
    MeasureTheory.ae_of_all _ fun b => by
      cases b <;> simp [X]
  have hm : AEMeasurable X (ProbabilityTheory.bernoulliMeasure true false q) :=
    (measurable_of_countable X).aemeasurable
  have hc : ∫ b, X b ∂(ProbabilityTheory.bernoulliMeasure true false q) = 0 := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp [X]
    ring
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm hb hc).mgf_le s
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_bernoulliMeasure] at h
  have hn : ((‖1 - (q : ℝ) - -(q : ℝ)‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    rw [show 1 - (q : ℝ) - -(q : ℝ) = 1 by ring]
    norm_num
  rw [hn] at h
  simp only [X, ite_true, Bool.false_eq_true, ite_false, smul_eq_mul] at h
  convert h using 2 <;> push_cast <;> ring_nf

variable {α : Type*} [Fintype α] [DecidableEq α]

section Hoeffding

variable {p : ℝ}

/-- The exponential moment of a weighted centred count. -/
theorem sum_biasedMass_mul_exp_le (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (d : α → ℝ) (t : ℝ) :
    ∑ s, biasedMass p s * exp (t * ∑ x, d x * ((if x ∈ s then 1 else 0) - p)) ≤
      exp ((∑ x, d x ^ 2) / 4 * t ^ 2 / 2) := by
  have key : ∀ s : Finset α, exp (t * ∑ x, d x * ((if x ∈ s then 1 else 0) - p)) =
      (∏ x ∈ s, exp (t * d x * (1 - p))) * ∏ x ∈ sᶜ, exp (-(t * d x * p)) := by
    intro s
    rw [Finset.mul_sum, exp_sum,
      ← Finset.prod_mul_prod_compl s (fun x => exp (t * (d x * ((if x ∈ s then 1 else 0) - p))))]
    congr 1
    · exact Finset.prod_congr rfl fun x hx => by rw [ite_eq_left hx]; ring_nf
    · exact Finset.prod_congr rfl fun x hx => by
        rw [ite_eq_right (Finset.mem_compl.mp hx)]; ring_nf
  simp_rw [key]
  rw [sum_biasedMass_mul_prod_mul_prod]
  calc ∏ x, (p * exp (t * d x * (1 - p)) + (1 - p) * exp (-(t * d x * p)))
      ≤ ∏ x, exp ((t * d x) ^ 2 / 8) :=
        Finset.prod_le_prod₀ (fun x _ => add_nonneg (mul_nonneg hp₀ (exp_pos _).le)
          (mul_nonneg (by linarith) (exp_pos _).le)) fun x _ => bernoulli_exp_le hp₀ hp₁ _
    _ = exp ((∑ x, d x ^ 2) / 4 * t ^ 2 / 2) := by
        rw [← exp_sum]
        congr 1
        rw [show (∑ x, d x ^ 2) / 4 * t ^ 2 / 2 = (∑ x, d x ^ 2) * (t ^ 2 / 8) by ring,
          Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

/-- Hoeffding's inequality, upper tail:
`P(∑ x, d x (1[x ∈ s] - p) ≥ u) ≤ exp(-2u² / ∑ d²)`. -/
theorem sum_biasedMass_hoeffding (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (d : α → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    ∑ s with u ≤ ∑ x, d x * ((if x ∈ s then 1 else 0) - p), biasedMass p s ≤
      exp (-(2 * u ^ 2 / ∑ x, d x ^ 2)) := by
  rcases (Finset.sum_nonneg fun x _ => sq_nonneg (d x) : 0 ≤ ∑ x, d x ^ 2).eq_or_lt with hD | hD
  · rw [← hD, div_zero, neg_zero, exp_zero]
    calc ∑ s with u ≤ ∑ x, d x * ((if x ∈ s then 1 else 0) - p), biasedMass p s
        ≤ ∑ s, biasedMass p s :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun s _ _ => biasedMass_nonneg hp₀ hp₁ s
      _ = 1 := sum_biasedMass p
  · have h := sum_filter_le_of_subgaussian (biasedMass p)
      (fun s => ∑ x, d x * ((if x ∈ s then 1 else 0) - p)) (biasedMass_nonneg hp₀ hp₁)
      (c := (∑ x, d x ^ 2) / 4) (by positivity)
      (fun t _ => sum_biasedMass_mul_exp_le hp₀ hp₁ d t |>.trans_eq (by ring_nf)) hu
    refine h.trans_eq ?_
    congr 1
    field_simp
    ring

/-- Hoeffding's inequality, lower tail. -/
theorem sum_biasedMass_hoeffding_lower (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (d : α → ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    ∑ s with ∑ x, d x * ((if x ∈ s then 1 else 0) - p) ≤ -u, biasedMass p s ≤
      exp (-(2 * u ^ 2 / ∑ x, d x ^ 2)) := by
  have h := sum_biasedMass_hoeffding hp₀ hp₁ (fun x => -d x) hu
  simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at h
  refine Eq.trans_le ?_ h
  refine Finset.sum_congr (Finset.filter_congr fun s _ => ?_) fun _ _ => rfl
  constructor <;> intro h' <;> linarith

omit [DecidableEq α] in
/-- If `|Y s| ≥ u` lies under the two one-sided events, the masses add. -/
theorem sum_filter_abs_le_add (w Y : Finset α → ℝ) (hw : ∀ s, 0 ≤ w s) (u : ℝ) :
    ∑ s with u ≤ |Y s|, w s ≤ ∑ s with u ≤ Y s, w s + ∑ s with Y s ≤ -u, w s := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have := hw s
  rcases abs_cases (Y s) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> split_ifs <;> linarith

/-- Hoeffding's inequality, two-sided: `P(|∑ x, d x (1[x ∈ s] - p)| ≥ u) ≤ 2 exp(-2u² / ∑ d²)`. -/
theorem sum_biasedMass_hoeffding_abs (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (d : α → ℝ) {u : ℝ}
    (hu : 0 ≤ u) :
    ∑ s with u ≤ |∑ x, d x * ((if x ∈ s then 1 else 0) - p)|, biasedMass p s ≤
      2 * exp (-(2 * u ^ 2 / ∑ x, d x ^ 2)) := by
  have h₁ := sum_biasedMass_hoeffding hp₀ hp₁ d hu
  have h₂ := sum_biasedMass_hoeffding_lower hp₀ hp₁ d hu
  have := sum_filter_abs_le_add (biasedMass p) (fun s => ∑ x, d x * ((if x ∈ s then 1 else 0) - p))
    (biasedMass_nonneg hp₀ hp₁) u
  linarith

/-- The centred count of a subset. -/
theorem sum_ite_mem_sub (p : ℝ) (s : Finset α) :
    ∑ x, ((if x ∈ s then 1 else 0) - p) = s.card - p * Fintype.card α := by
  rw [Finset.sum_sub_distrib]
  simp
  ring

/-- Hoeffding for the size: `P(|s| ≥ p n + u) ≤ exp(-2u²/n)` with `n = |α|`. -/
theorem sum_biasedMass_card_ge_le (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    ∑ s : Finset α with p * Fintype.card α + u ≤ s.card, biasedMass p s ≤
      exp (-(2 * u ^ 2 / Fintype.card α)) := by
  have h := sum_biasedMass_hoeffding hp₀ hp₁ (fun _ : α => (1 : ℝ)) hu
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sum_ite_mem_sub] at h
  refine Eq.trans_le ?_ h
  refine Finset.sum_congr (Finset.filter_congr fun s _ => ?_) fun _ _ => rfl
  constructor <;> intro h' <;> linarith

/-- Hoeffding for the size, lower tail: `P(|s| ≤ p n - u) ≤ exp(-2u²/n)`. -/
theorem sum_biasedMass_card_le_le (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    ∑ s : Finset α with (s.card : ℝ) ≤ p * Fintype.card α - u, biasedMass p s ≤
      exp (-(2 * u ^ 2 / Fintype.card α)) := by
  have h := sum_biasedMass_hoeffding_lower hp₀ hp₁ (fun _ : α => (1 : ℝ)) hu
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sum_ite_mem_sub] at h
  refine Eq.trans_le ?_ h
  refine Finset.sum_congr (Finset.filter_congr fun s _ => ?_) fun _ _ => rfl
  constructor <;> intro h' <;> linarith

/-- Hoeffding for the size, two-sided: `P(||s| - p n| ≥ u) ≤ 2 exp(-2u²/n)`. -/
theorem sum_biasedMass_card_abs_le (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {u : ℝ} (hu : 0 ≤ u) :
    ∑ s : Finset α with u ≤ |(s.card : ℝ) - p * Fintype.card α|, biasedMass p s ≤
      2 * exp (-(2 * u ^ 2 / Fintype.card α)) := by
  have h := sum_biasedMass_hoeffding_abs hp₀ hp₁ (fun _ : α => (1 : ℝ)) hu
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    sum_ite_mem_sub] at h
  exact h

end Hoeffding

section RelativeEntropy

/-- The relative entropy (in nats) of `Bernoulli a` from `Bernoulli p`. -/
def klBernoulli (a p : ℝ) : ℝ := a * log (a / p) + (1 - a) * log ((1 - a) / (1 - p))

/-- `klBernoulli a p` is the relative entropy of the two-point laws. -/
theorem klBernoulli_eq_relEntropy (a p : ℝ) :
    klBernoulli a p = relEntropy (fun b : Bool => if b then a else 1 - a)
      (fun b : Bool => if b then p else 1 - p) := by
  simp [klBernoulli, relEntropy]

theorem klBernoulli_one_sub (a p : ℝ) : klBernoulli (1 - a) (1 - p) = klBernoulli a p := by
  simp only [klBernoulli, sub_sub_cancel]
  ring

variable {p a : ℝ}

/-- The relative-entropy Chernoff bound: `P(|s| ≥ a n) ≤ exp(-n D(a‖p))` for `p ≤ a < 1`. -/
theorem sum_biasedMass_card_ge_le_exp_kl (hp : 0 < p) (hpa : p ≤ a) (ha : a < 1) :
    ∑ s : Finset α with a * Fintype.card α ≤ s.card, biasedMass p s ≤
      exp (-(Fintype.card α * klBernoulli a p)) := by
  have hp1 : 0 < 1 - p := by linarith
  have ha0 : 0 < a := hp.trans_le hpa
  have ha1 : 0 < 1 - a := by linarith
  set L := log (a / p) - log ((1 - a) / (1 - p)) with hL
  have hL0 : 0 ≤ L := by
    rw [hL, sub_nonneg]
    refine log_le_log (div_pos ha1 hp1) ?_
    calc (1 - a) / (1 - p) ≤ 1 := (div_le_one hp1).mpr (by linarith)
      _ ≤ a / p := (one_le_div hp).mpr hpa
  have hbase : p * exp L + (1 - p) = (1 - p) / (1 - a) := by
    rw [hL, exp_sub, exp_log (div_pos ha0 hp), exp_log (div_pos ha1 hp1)]
    field_simp
    ring
  have hmom : ∑ s : Finset α, biasedMass p s * exp (L * s.card) =
      ((1 - p) / (1 - a)) ^ Fintype.card α := by
    have h := sum_biasedMass_mul_prod_mul_prod (α := α) p (fun _ => exp L) (fun _ => 1)
    simp only [Finset.prod_const, one_pow, mul_one, hbase, Finset.card_univ] at h
    rw [← h]
    exact Finset.sum_congr rfl fun s _ => by rw [mul_comm L, exp_nat_mul]
  have h := sum_filter_le_exp_mul_sum (biasedMass p) (fun s : Finset α => (s.card : ℝ))
    (biasedMass_nonneg hp.le (by linarith)) hL0 (a * Fintype.card α)
  beta_reduce at h
  rw [hmom] at h
  refine h.trans_eq ?_
  have hk : -(Fintype.card α * klBernoulli a p) =
      -(L * (a * Fintype.card α)) + Fintype.card α * log ((1 - p) / (1 - a)) := by
    rw [hL, klBernoulli, log_div ha0.ne' hp.ne', log_div ha1.ne' hp1.ne',
      log_div hp1.ne' ha1.ne']
    ring
  rw [hk, exp_add, exp_nat_mul, exp_log (div_pos hp1 ha1)]

/-- The lower relative-entropy Chernoff bound: `P(|s| ≤ a n) ≤ exp(-n D(a‖p))` for
`0 < a ≤ p < 1`. -/
theorem sum_biasedMass_card_le_le_exp_kl (hp : p < 1) (hap : a ≤ p) (ha : 0 < a) :
    ∑ s : Finset α with (s.card : ℝ) ≤ a * Fintype.card α, biasedMass p s ≤
      exp (-(Fintype.card α * klBernoulli a p)) := by
  have h := sum_biasedMass_card_ge_le_exp_kl (α := α) (p := 1 - p) (a := 1 - a) (by linarith)
    (by linarith) (by linarith)
  rw [klBernoulli_one_sub] at h
  refine Eq.trans_le ?_ h
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.ofBijective compl compl_involutive.bijective) _ _ fun s => ?_
  simp only [Equiv.ofBijective_apply, biasedMass_compl, sub_sub_cancel]
  have hc : ((sᶜ.card : ℕ) : ℝ) = Fintype.card α - s.card := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ s)]
  refine if_congr ?_ rfl rfl
  rw [hc]
  constructor <;> intro h' <;> linarith

/-- The multiplicative Chernoff bound: for `δ ≥ 0`,
`P(|s| ≥ (1+δ) p n) ≤ exp(-p n ((1+δ) log(1+δ) - δ))`. -/
theorem sum_biasedMass_card_ge_le_exp_mul (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ s : Finset α with (1 + δ) * p * Fintype.card α ≤ s.card, biasedMass p s ≤
      exp (-(p * Fintype.card α * ((1 + δ) * log (1 + δ) - δ))) := by
  have hδ1 : 0 < 1 + δ := by linarith
  have hmom : ∑ s : Finset α, biasedMass p s * exp (log (1 + δ) * s.card) =
      (1 + p * δ) ^ Fintype.card α := by
    have h := sum_biasedMass_mul_prod_mul_prod (α := α) p (fun _ => 1 + δ) (fun _ => 1)
    simp only [Finset.prod_const, one_pow, mul_one, Finset.card_univ] at h
    rw [show 1 + p * δ = p * (1 + δ) + (1 - p) by ring, ← h]
    exact Finset.sum_congr rfl fun s _ => by rw [mul_comm (log (1 + δ)), exp_nat_mul, exp_log hδ1]
  have h := sum_filter_le_exp_mul_sum (biasedMass p) (fun s : Finset α => (s.card : ℝ))
    (biasedMass_nonneg hp₀ hp₁) (log_nonneg (by linarith : (1 : ℝ) ≤ 1 + δ))
    ((1 + δ) * p * Fintype.card α)
  beta_reduce at h
  rw [hmom] at h
  refine h.trans ?_
  calc exp (-(log (1 + δ) * ((1 + δ) * p * Fintype.card α))) * (1 + p * δ) ^ Fintype.card α
      ≤ exp (-(log (1 + δ) * ((1 + δ) * p * Fintype.card α))) * exp (p * δ) ^ Fintype.card α :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by nlinarith)
          (by linarith [add_one_le_exp (p * δ)]) _) (exp_pos _).le
    _ = exp (-(p * Fintype.card α * ((1 + δ) * log (1 + δ) - δ))) := by
        rw [← exp_nat_mul, ← exp_add]
        congr 1
        ring

/-- The counting form for `p = 1/2`: at most `2^n exp(-2u²/n)` subsets have size
`≥ n/2 + u`. -/
theorem card_filter_card_ge_le {u : ℝ} (hu : 0 ≤ u) :
    ((univ.filter fun s : Finset α => (Fintype.card α : ℝ) / 2 + u ≤ s.card).card : ℝ) ≤
      2 ^ Fintype.card α * exp (-(2 * u ^ 2 / Fintype.card α)) := by
  have h := sum_biasedMass_card_ge_le (α := α) (p := 1 / 2) (by norm_num) (by norm_num) hu
  have hm : ∀ s : Finset α, biasedMass (1 / 2) s = (1 / 2) ^ Fintype.card α := by
    intro s
    rw [biasedMass]
    norm_num
    rw [one_div, inv_pow]
  simp only [hm, Finset.sum_const, nsmul_eq_mul] at h
  rw [show (1 / 2 : ℝ) * Fintype.card α = Fintype.card α / 2 by ring] at h
  have h2 : (2 : ℝ) ^ Fintype.card α * (1 / 2) ^ Fintype.card α = 1 := by
    rw [← mul_pow]; norm_num
  calc ((univ.filter fun s : Finset α => (Fintype.card α : ℝ) / 2 + u ≤ s.card).card : ℝ)
      = 2 ^ Fintype.card α * (((univ.filter fun s : Finset α =>
          (Fintype.card α : ℝ) / 2 + u ≤ s.card).card : ℝ) * (1 / 2) ^ Fintype.card α) := by
        rw [mul_left_comm, h2, mul_one]
    _ ≤ 2 ^ Fintype.card α * exp (-(2 * u ^ 2 / Fintype.card α)) :=
        mul_le_mul_of_nonneg_left h (by positivity)

/-- Configurations to subsets: the number of `true` coordinates of `configOf s` is `|s|`. -/
theorem card_filter_configOf (s : Finset α) :
    (univ.filter fun e => configOf s e = true).card = s.card :=
  congrArg Finset.card (configEquiv.right_inv s)

end RelativeEntropy

end

end TheoremOS.Probability
