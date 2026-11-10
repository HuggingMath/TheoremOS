import Submission.Library.TheoremOS.BooleanCube.Fourier

/-!
# Polynomials evaluated on the Boolean cube

Evaluating `p : MvPolynomial ι ℝ` at `x ↦ (sign (x i))ᵢ` collapses each monomial `X^m` to the
character of its odd-exponent support `oddSupport m`, since `sign b ^ 2 = 1`. Hence
`f̂ S = ∑_{m ∈ supp p, oddSupport m = S} p.coeff m`, the Fourier degree is at most
`p.totalDegree`, and for multilinear `p` (all exponents `≤ 1`) the Fourier coefficients are the
polynomial coefficients and the Fourier degree equals the total degree. Complementing every input
bit multiplies `f̂ S` by `(-1)^|S|` and preserves the degree, which covers the encoding
`true ↦ 1, false ↦ -1`.

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Chapter 1 (Theorem 1.1 and §1.3: the multilinear expansion is the Fourier expansion and is
unique). Textbook material.

Bridges: `(if x i then 1 else -1) = sign (!(x i))` (`ite_one_neg_one_eq_sign_not`), so
`eval (fun i => if x i then 1 else -1) p` is `evalSign p (complement x)`
(`eval_ite_one_neg_one_eq`); `degree_eval_ite_one_neg_one_le` bounds its Fourier degree by
`p.totalDegree`.
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- The coordinates with odd exponent. -/
def oddSupport (m : ι →₀ ℕ) : Finset ι := m.support.filter fun i => Odd (m i)

lemma card_oddSupport_le (m : ι →₀ ℕ) : (oddSupport m).card ≤ m.sum fun _ e => e := by
  rw [oddSupport, card_filter, Finsupp.sum]
  exact sum_le_sum fun i _ => by split_ifs with h; exacts [h.pos, Nat.zero_le _]

lemma oddSupport_eq_support {m : ι →₀ ℕ} (hm : ∀ i, m i ≤ 1) : oddSupport m = m.support := by
  ext i
  simp only [oddSupport, mem_filter, Finsupp.mem_support_iff, and_iff_left_iff_imp]
  intro h
  have : m i = 1 := by have := hm i; omega
  rw [this]; exact odd_one

lemma sign_pow_eq_ite (b : Bool) (k : ℕ) : sign b ^ k = if Odd k then sign b else 1 := by
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    rw [pow_succ, pow_mul, sign_sq, one_pow, one_mul]
  · obtain ⟨r, rfl⟩ := Nat.not_odd_iff_even.1 h
    rw [← two_mul, pow_mul, sign_sq, one_pow]

lemma prod_sign_pow (m : ι →₀ ℕ) (x : ι → Bool) :
    ∏ i ∈ m.support, sign (x i) ^ m i = character (oddSupport m) x := by
  rw [character, oddSupport, prod_filter]
  exact prod_congr rfl fun i _ => sign_pow_eq_ite _ _

/-- The function `x ↦ p((sign (x i))ᵢ)` on the cube. -/
def evalSign (p : MvPolynomial ι ℝ) (x : ι → Bool) : ℝ := MvPolynomial.eval (fun i => sign (x i)) p

theorem evalSign_eq_sum (p : MvPolynomial ι ℝ) (x : ι → Bool) :
    evalSign p x = ∑ m ∈ p.support, p.coeff m * character (oddSupport m) x := by
  simp only [evalSign, MvPolynomial.eval_eq, prod_sign_pow]

/-- Complement every bit. -/
def complement (x : ι → Bool) : ι → Bool := fun i => !(x i)

@[simp] lemma complement_complement (x : ι → Bool) : complement (complement x) = x := by
  funext i; simp [complement]

/-- Complementation as an involution of the cube. -/
def complementEquiv : (ι → Bool) ≃ (ι → Bool) where
  toFun := complement
  invFun := complement
  left_inv := complement_complement
  right_inv := complement_complement

lemma character_complement (S : Finset ι) (x : ι → Bool) :
    character S (complement x) = (-1) ^ S.card * character S x := by
  simp only [character, complement, sign_not, prod_neg]

lemma ite_one_neg_one_eq_sign_not (b : Bool) : (if b then (1 : ℝ) else -1) = sign (!b) := by
  cases b <;> rfl

lemma eval_ite_one_neg_one_eq (p : MvPolynomial ι ℝ) (x : ι → Bool) :
    MvPolynomial.eval (fun i => if x i then (1 : ℝ) else -1) p = evalSign p (complement x) := by
  simp only [evalSign, complement, ite_one_neg_one_eq_sign_not]

variable [Fintype ι] [DecidableEq ι]

/-- `f̂ S = ∑_{m ∈ supp p, oddSupport m = S} p.coeff m` for `f = evalSign p`. -/
theorem fourierCoeff_evalSign (p : MvPolynomial ι ℝ) (S : Finset ι) :
    fourierCoeff (evalSign p) S = ∑ m ∈ p.support with oddSupport m = S, p.coeff m := by
  have h : evalSign p = fun x => ∑ T, (∑ m ∈ p.support with oddSupport m = T, p.coeff m) * character T x := by
    funext x
    rw [evalSign_eq_sum]
    simp only [sum_mul]
    exact (sum_fiberwise p.support oddSupport fun m => p.coeff m * character (oddSupport m) x).symm.trans
      (sum_congr rfl fun T _ => sum_congr rfl fun m hm => by rw [(mem_filter.1 hm).2])
  rw [h, fourierCoeff_sum_character]

/-- The Fourier degree of `evalSign p` is at most `p.totalDegree`. -/
theorem degree_evalSign_le (p : MvPolynomial ι ℝ) : degree (evalSign p) ≤ p.totalDegree := by
  rw [degree_le_iff]
  intro S hS
  rw [fourierCoeff_evalSign] at hS
  obtain ⟨m, hm, -⟩ := exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨hmp, rfl⟩ := mem_filter.1 hm
  exact (card_oddSupport_le m).trans (MvPolynomial.le_totalDegree hmp)

/-- For multilinear `p`, `f̂ (supp m) = p.coeff m` for each monomial `m` of `p`. -/
theorem fourierCoeff_evalSign_support {p : MvPolynomial ι ℝ} (hp : ∀ m ∈ p.support, ∀ i, m i ≤ 1)
    {m : ι →₀ ℕ} (hm : m ∈ p.support) : fourierCoeff (evalSign p) m.support = p.coeff m := by
  rw [fourierCoeff_evalSign, sum_eq_single_of_mem m (mem_filter.2 ⟨hm, oddSupport_eq_support (hp m hm)⟩)]
  intro m' hm' hne
  exfalso
  obtain ⟨hm'p, hodd⟩ := mem_filter.1 hm'
  rw [oddSupport_eq_support (hp m' hm'p)] at hodd
  apply hne
  ext i
  have h1 := hp m hm i
  have h2 := hp m' hm'p i
  have h3 : m' i ≠ 0 ↔ m i ≠ 0 := by
    rw [← Finsupp.mem_support_iff, ← Finsupp.mem_support_iff, hodd]
  omega

/-- For multilinear `p`, the Fourier degree of `evalSign p` equals `p.totalDegree`. -/
theorem degree_evalSign_of_multilinear {p : MvPolynomial ι ℝ} (hp : ∀ m ∈ p.support, ∀ i, m i ≤ 1) :
    degree (evalSign p) = p.totalDegree := by
  refine le_antisymm (degree_evalSign_le p) ?_
  rcases p.support.eq_empty_or_nonempty with h | h
  · simp [MvPolynomial.totalDegree, h]
  obtain ⟨m, hm, hsup⟩ := exists_mem_eq_sup p.support h fun s => s.sum fun _ e => e
  rw [MvPolynomial.totalDegree, hsup]
  have hcard : (m.sum fun _ e => e) = m.support.card := by
    rw [card_eq_sum_ones, Finsupp.sum]
    exact sum_congr rfl fun i hi => by
      have := hp m hm i; have := Finsupp.mem_support_iff.1 hi; omega
  rw [hcard]
  apply card_le_degree
  rw [fourierCoeff_evalSign_support hp hm]
  exact MvPolynomial.mem_support_iff.1 hm

/-- `(f ∘ complement)^ S = (-1)^|S| f̂ S`. -/
theorem fourierCoeff_comp_complement (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f (complement x)) S = (-1) ^ S.card * fourierCoeff f S := by
  unfold fourierCoeff
  rw [← average_comp_equiv complementEquiv, ← average_const_mul]
  refine average_congr fun x => ?_
  change f (complement (complement x)) * character S (complement x) = _
  rw [complement_complement, character_complement]; ring

theorem degree_comp_complement (f : (ι → Bool) → ℝ) : degree (fun x => f (complement x)) = degree f := by
  unfold degree
  congr 1
  ext S
  simp only [mem_filter, mem_univ, true_and, fourierCoeff_comp_complement, ne_eq, mul_eq_zero,
    pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or]

/-- With the encoding `true ↦ 1, false ↦ -1` the Fourier degree is still at most the total degree. -/
theorem degree_eval_ite_one_neg_one_le (p : MvPolynomial ι ℝ) :
    degree (fun x : ι → Bool => MvPolynomial.eval (fun i => if x i then (1 : ℝ) else -1) p) ≤ p.totalDegree := by
  simp only [eval_ite_one_neg_one_eq]
  rw [degree_comp_complement]
  exact degree_evalSign_le p

end

end TheoremOS.BooleanCube
