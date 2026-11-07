import Mathlib

/-!
# Binomial coefficients and the binary entropy function

Entropy estimates for binomial coefficients, with `Real.binEntropy p = p log p⁻¹ + (1-p) log (1-p)⁻¹`
in nats. Contents: the binomial probabilities `binomTerm n p j = C(n,j) p^j (1-p)^(n-j)`, their sum
and bounds, unimodality around `n p`; `C(n,k) ≤ exp (n H(k/n))`; the Hamming-ball bound
`∑_{j ≤ k} C(n,j) ≤ exp (n H(k/n))` for `2k ≤ n`; the reverse bound
`exp (n H(k/n)) ≤ (n+1) C(n,k)`; `C(n,k) ≤ (e n / k)^k`; `(1 - p)^n ≤ exp (-p n)`; and the count of
subsets of size at most `k`.

Sources: T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley, 2006,
Section 11.1 (method of types, Theorem 11.1.3 and Example 11.1.3: `C(n,k)` within a factor
`n + 1` of `exp (n H(k/n))`); J. Flum and M. Grohe, *Parameterized Complexity Theory*, Springer,
2006, Lemma 16.19 (`∑_{j ≤ αn} C(n,j) ≤ 2^{H(α) n}` for `α ≤ 1/2`); S. Jukna, *Extremal
Combinatorics*, 2nd ed., Springer, 2011, Section 1.3 (`C(n,k) ≤ (en/k)^k`). Textbook material;
nothing here is specific to a benchmark problem.

Bridges: base-2 entropy is `binEntropy p / log 2`, so `exp (n H(p)) = 2 ^ (n H₂(p))` by
`Real.rpow_def_of_pos`; the number of `s : Finset ι` with `s.card ≤ k` is
`card_filter_card_le`.
-/

namespace TheoremOS.Combinatorics

open Finset Real
open scoped BigOperators

noncomputable section

/-- The binomial probability `C(n,j) p^j (1-p)^(n-j)`. -/
def binomTerm (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := n.choose j * p ^ j * (1 - p) ^ (n - j)

lemma sum_binomTerm (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), binomTerm n p j = 1 := by
  have h := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [binomTerm]
  ring

lemma binomTerm_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    0 ≤ binomTerm n p j := by
  unfold binomTerm
  have : 0 ≤ 1 - p := by linarith
  positivity

lemma binomTerm_le_one {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {j : ℕ} (hj : j ≤ n) :
    binomTerm n p j ≤ 1 := by
  rw [← sum_binomTerm n p]
  exact Finset.single_le_sum (fun i _ => binomTerm_nonneg n hp0 hp1 i)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))

lemma binomTerm_of_lt {n : ℕ} (p : ℝ) {j : ℕ} (hj : n < j) : binomTerm n p j = 0 := by
  simp [binomTerm, Nat.choose_eq_zero_of_lt hj]

/-- `binEntropy` in the form `-p log p - (1-p) log (1-p)`. -/
lemma binEntropy_eq_neg (p : ℝ) : binEntropy p = -(p * log p) - (1 - p) * log (1 - p) := by
  rw [binEntropy, log_inv, log_inv]
  ring

/-- The type-class probability: `(k/n)^k (1-k/n)^(n-k) = exp (-n H(k/n))`. -/
theorem pow_mul_pow_eq_exp_neg_binEntropy {n k : ℕ} (hk : k ≤ n) (hn : 0 < n) :
    ((k : ℝ) / n) ^ k * (1 - (k : ℝ) / n) ^ (n - k) = exp (-(n * binEntropy ((k : ℝ) / n))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  rcases hk.lt_or_eq with hkn | rfl
  · set p : ℝ := k / n with hpdef
    have hp : 0 < p := by positivity
    have hq : 0 < 1 - p := by
      rw [sub_pos, hpdef, div_lt_one hn']
      exact_mod_cast hkn
    have hnp : (n : ℝ) * p = k := by rw [hpdef]; field_simp
    have hnq : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk, mul_sub, mul_one, hnp]
    have hpos : 0 < p ^ k * (1 - p) ^ (n - k) := by positivity
    rw [← exp_log hpos, log_mul (pow_pos hp k).ne' (pow_pos hq _).ne', log_pow, log_pow,
      binEntropy_eq_neg]
    congr 1
    linear_combination (-log p) * hnp - log (1 - p) * hnq
  · simp [div_self hn'.ne']

/-- `C(n,k) ≤ exp (n H(k/n))`. -/
theorem choose_le_exp_binEntropy (n k : ℕ) :
    (n.choose k : ℝ) ≤ exp (n * binEntropy ((k : ℝ) / n)) := by
  rcases Nat.lt_or_ge n k with hnk | hkn
  · rw [Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero]
    exact (exp_pos _).le
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : (0 : ℝ) ≤ k / n := by positivity
  have hp1 : (k : ℝ) / n ≤ 1 := by rw [div_le_one hn']; exact_mod_cast hkn
  have h := binomTerm_le_one hp0 hp1 hkn
  rw [binomTerm, mul_assoc, pow_mul_pow_eq_exp_neg_binEntropy hkn hn] at h
  rwa [← le_div_iff₀ (exp_pos _), one_div, ← exp_neg, neg_neg] at h

/-- For `p ≤ 1/2` and `j ≤ k`, `p^j (1-p)^(n-j) ≥ p^k (1-p)^(n-k)`. -/
lemma pow_mul_pow_le_of_le {n j k : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 - p) (hjk : j ≤ k)
    (hkn : k ≤ n) : p ^ k * (1 - p) ^ (n - k) ≤ p ^ j * (1 - p) ^ (n - j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have hq : 0 ≤ 1 - p := hp0.trans hp
  have hsplit : n - j = (n - (j + d)) + d := by omega
  rw [hsplit, pow_add, pow_add]
  have h1 : p ^ d ≤ (1 - p) ^ d := pow_le_pow_left₀ hp0 hp d
  calc p ^ j * p ^ d * (1 - p) ^ (n - (j + d))
      = p ^ j * (1 - p) ^ (n - (j + d)) * p ^ d := by ring
    _ ≤ p ^ j * (1 - p) ^ (n - (j + d)) * (1 - p) ^ d := by gcongr
    _ = p ^ j * ((1 - p) ^ (n - (j + d)) * (1 - p) ^ d) := by ring

/-- The Hamming-ball bound `∑_{j ≤ k} C(n,j) ≤ exp (n H(k/n))` for `2k ≤ n`. -/
theorem sum_choose_le_exp_binEntropy {n k : ℕ} (hk : 2 * k ≤ n) :
    (∑ j ∈ range (k + 1), (n.choose j : ℝ)) ≤ exp (n * binEntropy ((k : ℝ) / n)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  have hn : 0 < n := by omega
  have hkn : k ≤ n := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := k / n with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hn']; exact_mod_cast hkn
  have hhalf : p ≤ 1 - p := by
    have : (2 * k : ℝ) ≤ n := by exact_mod_cast hk
    rw [hpdef, le_sub_iff_add_le, ← two_mul, mul_div_assoc', div_le_one hn']
    linarith
  have hT := pow_mul_pow_eq_exp_neg_binEntropy hkn hn
  rw [← hpdef] at hT
  have hsum : (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * exp (-(n * binEntropy p)) ≤ 1 := by
    calc (∑ j ∈ range (k + 1), (n.choose j : ℝ)) * exp (-(n * binEntropy p))
        = ∑ j ∈ range (k + 1), (n.choose j : ℝ) * (p ^ k * (1 - p) ^ (n - k)) := by
          rw [Finset.sum_mul, hT]
      _ ≤ ∑ j ∈ range (k + 1), binomTerm n p j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [binomTerm, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (pow_mul_pow_le_of_le hp0 hhalf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hkn)
            (Nat.cast_nonneg _)
      _ ≤ ∑ j ∈ range (n + 1), binomTerm n p j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            fun j _ _ => binomTerm_nonneg n hp0 hp1 j
      _ = 1 := sum_binomTerm n p
  rwa [← le_div_iff₀ (exp_pos _), one_div, ← exp_neg, neg_neg] at hsum

/-! ### Unimodality and the reverse bound -/

/-- The ratio step `C(n,j+1) (n-j)⁻¹ = C(n,j) (j+1)⁻¹`, cleared of denominators. -/
lemma binomTerm_step {n j : ℕ} (hj : j < n) (p : ℝ) :
    binomTerm n p (j + 1) * ((j : ℝ) + 1) * (1 - p) =
      binomTerm n p j * ((n : ℝ) - j) * p := by
  have hc : (n.choose (j + 1) : ℝ) * ((j : ℝ) + 1) = n.choose j * ((n : ℝ) - j) := by
    have := Nat.choose_succ_right_eq n j
    rw [← Nat.cast_sub hj.le]
    exact_mod_cast this
  have hsplit : n - j = (n - (j + 1)) + 1 := by omega
  simp only [binomTerm]
  rw [hsplit, pow_succ, pow_succ]
  linear_combination (p ^ j * p * (1 - p) ^ (n - (j + 1)) * (1 - p)) * hc

lemma binomTerm_le_succ {n j : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hj : j < n)
    (h : ((j : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - j) * p) :
    binomTerm n p j ≤ binomTerm n p (j + 1) := by
  have hstep := binomTerm_step hj p
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hnj : (0 : ℝ) < (n : ℝ) - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hT0 := binomTerm_nonneg n hp0 hp1 j
  have hT1 := binomTerm_nonneg n hp0 hp1 (j + 1)
  -- `T_j (j+1)(1-p) ≤ T_j (n-j) p = T_{j+1} (j+1)(1-p)`, so compare after scaling by `(n-j) p`.
  by_cases hq : p = 1
  · subst hq
    simp only [sub_self, mul_zero, mul_one] at hstep
    have : binomTerm n 1 j = 0 := by
      have := mul_eq_zero.1 hstep.symm
      rcases this with h0 | h0
      · exact h0
      · exact absurd h0 hnj.ne'
    rw [this]
    exact hT1
  have hq0 : 0 < 1 - p := by
    rcases hp1.lt_or_eq with h1 | h1
    · linarith
    · exact absurd h1 hq
  have key : binomTerm n p j * (((j : ℝ) + 1) * (1 - p)) ≤
      binomTerm n p (j + 1) * (((j : ℝ) + 1) * (1 - p)) := by
    calc binomTerm n p j * (((j : ℝ) + 1) * (1 - p))
        ≤ binomTerm n p j * (((n : ℝ) - j) * p) := mul_le_mul_of_nonneg_left h hT0
      _ = binomTerm n p (j + 1) * (((j : ℝ) + 1) * (1 - p)) := by linear_combination -hstep
  exact le_of_mul_le_mul_right key (by positivity)

lemma binomTerm_succ_le {n j : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hj : j < n)
    (h : ((n : ℝ) - j) * p ≤ ((j : ℝ) + 1) * (1 - p)) :
    binomTerm n p (j + 1) ≤ binomTerm n p j := by
  have hstep := binomTerm_step hj p
  have hnj : (0 : ℝ) < (n : ℝ) - j := by
    have : (j : ℝ) < n := by exact_mod_cast hj
    linarith
  have hT0 := binomTerm_nonneg n hp0 hp1 j
  have hT1 := binomTerm_nonneg n hp0 hp1 (j + 1)
  rcases hp0.lt_or_eq with hp | rfl
  · have key : binomTerm n p (j + 1) * (((n : ℝ) - j) * p) ≤
        binomTerm n p j * (((n : ℝ) - j) * p) := by
      calc binomTerm n p (j + 1) * (((n : ℝ) - j) * p)
          ≤ binomTerm n p (j + 1) * (((j : ℝ) + 1) * (1 - p)) := mul_le_mul_of_nonneg_left h hT1
        _ = binomTerm n p j * (((n : ℝ) - j) * p) := by linear_combination hstep
    exact le_of_mul_le_mul_right key (by positivity)
  · have : binomTerm n 0 (j + 1) = 0 := by simp [binomTerm]
    rw [this]
    exact hT0

lemma binomTerm_le_of_steps_up {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (j : ℕ) :
    ∀ d, j + d ≤ n → (∀ i, j ≤ i → i < j + d → ((i : ℝ) + 1) * (1 - p) ≤ ((n : ℝ) - i) * p) →
      binomTerm n p j ≤ binomTerm n p (j + d)
  | 0, _, _ => le_rfl
  | d + 1, hd, h =>
    (binomTerm_le_of_steps_up hp0 hp1 j d (by omega) fun i hi hid => h i hi (by omega)).trans
      (binomTerm_le_succ hp0 hp1 (by omega) (h (j + d) (by omega) (by omega)))

lemma binomTerm_le_of_steps_down {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    ∀ d, k + d ≤ n → (∀ i, k ≤ i → i < k + d → ((n : ℝ) - i) * p ≤ ((i : ℝ) + 1) * (1 - p)) →
      binomTerm n p (k + d) ≤ binomTerm n p k
  | 0, _, _ => le_rfl
  | d + 1, hd, h =>
    (binomTerm_succ_le hp0 hp1 (by omega) (h (k + d) (by omega) (by omega))).trans
      (binomTerm_le_of_steps_down hp0 hp1 k d (by omega) fun i hi hid => h i hi (by omega))

/-- The binomial probabilities at `p = k/n` peak at `k`. -/
theorem binomTerm_le_binomTerm_self {n k j : ℕ} (hkn : k ≤ n) (hn : 0 < n) :
    binomTerm n ((k : ℝ) / n) j ≤ binomTerm n ((k : ℝ) / n) k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := k / n with hpdef
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by rw [hpdef, div_le_one hn']; exact_mod_cast hkn
  have hnp : (n : ℝ) * p = k := by rw [hpdef]; field_simp
  have hdiff : ∀ i : ℕ, ((n : ℝ) - i) * p - ((i : ℝ) + 1) * (1 - p) = k + p - (i + 1) := by
    intro i
    linear_combination hnp
  rcases Nat.lt_or_ge n j with hnj | hjn
  · rw [binomTerm_of_lt p hnj]
    exact binomTerm_nonneg n hp0 hp1 k
  rcases le_or_gt j k with hjk | hkj
  · have h := binomTerm_le_of_steps_up (n := n) hp0 hp1 j (k - j) (by omega) fun i _ hi => by
      have h1 : (i : ℝ) + 1 ≤ k := by exact_mod_cast (show i + 1 ≤ k by omega)
      linarith [hdiff i]
    rwa [Nat.add_sub_cancel' hjk] at h
  · have h := binomTerm_le_of_steps_down (n := n) hp0 hp1 k (j - k) (by omega) fun i hi _ => by
      have h1 : (k : ℝ) ≤ i := by exact_mod_cast hi
      linarith [hdiff i]
    rwa [Nat.add_sub_cancel' hkj.le] at h

/-- The reverse bound `exp (n H(k/n)) ≤ (n+1) C(n,k)`. -/
theorem exp_binEntropy_le_succ_mul_choose {n k : ℕ} (hkn : k ≤ n) :
    exp (n * binEntropy ((k : ℝ) / n)) ≤ (n + 1) * n.choose k := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set p : ℝ := k / n with hpdef
  have hsum : (1 : ℝ) ≤ (n + 1) * binomTerm n p k := by
    calc (1 : ℝ) = ∑ j ∈ range (n + 1), binomTerm n p j := (sum_binomTerm n p).symm
      _ ≤ ∑ _j ∈ range (n + 1), binomTerm n p k :=
          Finset.sum_le_sum fun j _ => binomTerm_le_binomTerm_self hkn hn
      _ = (n + 1) * binomTerm n p k := by simp
  have hT := pow_mul_pow_eq_exp_neg_binEntropy hkn hn
  rw [← hpdef] at hT
  rw [binomTerm, mul_assoc, hT, exp_neg] at hsum
  have he := exp_pos (n * binEntropy p)
  calc exp (n * binEntropy p) = exp (n * binEntropy p) * 1 := (mul_one _).symm
    _ ≤ exp (n * binEntropy p) * ((n + 1) * (n.choose k * (exp (n * binEntropy p))⁻¹)) := by
        gcongr
    _ = (n + 1) * n.choose k := by field_simp

/-- `C(n,k) ≤ (e n / k)^k`. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (exp 1 * n / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hfac : (k : ℝ) ^ k / k.factorial ≤ exp k := pow_div_factorial_le_exp _ hk'.le k
  have hfpos : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  calc (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k n
    _ = ((n : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
        rw [div_pow]
        field_simp
    _ ≤ ((n : ℝ) / k) ^ k * exp k := by gcongr
    _ = (exp 1 * n / k) ^ k := by
        rw [show (k : ℝ) = k * 1 by ring, exp_nat_mul, mul_one, ← mul_pow]
        ring

/-- `(1 - p)^n ≤ exp (-p n)` for `p ≤ 1`. -/
theorem one_sub_pow_le_exp_neg {p : ℝ} (hp : p ≤ 1) (n : ℕ) : (1 - p) ^ n ≤ exp (-(p * n)) := by
  have h1 : 1 - p ≤ exp (-p) := by linarith [add_one_le_exp (-p)]
  calc (1 - p) ^ n ≤ exp (-p) ^ n := pow_le_pow_left₀ (by linarith) h1 n
    _ = exp (-(p * n)) := by rw [← exp_nat_mul]; ring_nf

/-- The number of subsets of `s` with at most `k` elements. -/
theorem card_filter_card_le {α : Type*} (s : Finset α) (k : ℕ) :
    (s.powerset.filter fun t => t.card ≤ k).card = ∑ j ∈ range (k + 1), s.card.choose j := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [← card_powersetCard]
    congr 1
    ext t
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    have := Finset.mem_range.1 hj
    constructor
    · rintro ⟨⟨hts, -⟩, rfl⟩
      exact ⟨hts, rfl⟩
    · rintro ⟨hts, rfl⟩
      exact ⟨⟨hts, by omega⟩, rfl⟩
  · intro t ht
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powerset] at ht
    simp only [coe_range, Set.mem_Iio]
    omega

end

end TheoremOS.Combinatorics
