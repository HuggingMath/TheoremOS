import Submission.Library.TheoremOS.Probability.FiniteProbability

/-!
# The Lovász Local Lemma

The finite-weight **Lovász Local Lemma** in its lopsided asymmetric form, its symmetric
corollary, and the product-measure bridge that supplies its dependency hypothesis. Contents:
`avoid A T`, the outcomes in none of the events `A i` with `i ∈ T`; the **lopsided dependency**
condition `IsLopsidedDependency A p N`: `P(A i ∩ avoid T) ≤ P(A i) P(avoid T)` whenever `T` misses
`i` and its neighbourhood `N i`; the **asymmetric LLL**: if `0 ≤ x i < 1` and
`P(A i) ≤ x i ∏_{j ∈ N i} (1 - x j)`, then `P(no A i) ≥ ∏ (1 - x i) > 0`, so some outcome avoids
every event; the conditional form `P(A i ∩ avoid T) ≤ x i P(avoid T)` that drives it; the
**symmetric LLL**: `e q (d + 1) ≤ 1` with `P(A i) ≤ q` and `|N i| ≤ d` suffices; the estimate
`exp (-1) ≤ (1 - 1/(d+1))^d`; and for a **product measure** on `κ → α`, independence of events
determined by disjoint coordinate sets, which gives lopsided dependency for events with
variable sets `vbl i` when `N i` contains every `j ≠ i` whose variables meet `vbl i`.

Sources: P. Erdős and L. Lovász, Problems and results on 3-chromatic hypergraphs and some related
questions (1975); J. Spencer, Asymptotic lower bounds for Ramsey functions, Discrete Math. 20
(1977); N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, Chapter 5
(Lemma 5.1.1, Corollary 5.1.2). Textbook material; nothing here is specific to a benchmark problem.

Bridges: outcomes are a `Fintype Ω` with weights `p : Ω → ℝ` (`IsDistribution p`); events are
`A : ι → Finset Ω` and a neighbourhood is `N : ι → Finset ι`. For random assignments
`ω : κ → α` with independent coordinates of law `μ`, `p = productWeight μ`; an event that only
reads the coordinates in `V` is `DependsOn A V`, and `isLopsidedDependency_of_dependsOn` turns
a variable-set description into the dependency hypothesis.
-/

namespace TheoremOS.Probability

open Finset
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

section Avoid

variable {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The outcomes in none of the events `A i`, `i ∈ T`. -/
def avoid (A : ι → Finset Ω) (T : Finset ι) : Finset Ω := {ω | ∀ i ∈ T, ω ∉ A i}

variable (A : ι → Finset Ω)

lemma mem_avoid {T : Finset ι} {ω : Ω} : ω ∈ avoid A T ↔ ∀ i ∈ T, ω ∉ A i := by
  simp [avoid]

@[simp] lemma avoid_empty : avoid A ∅ = Finset.univ := by
  ext ω
  simp [mem_avoid]

lemma avoid_anti {T T' : Finset ι} (h : T ⊆ T') : avoid A T' ⊆ avoid A T := fun _ hω =>
  (mem_avoid A).2 fun i hi => (mem_avoid A).1 hω i (h hi)

/-- **Lopsided dependency**: avoiding events outside the neighbourhood `N i` does not make
`A i` more likely. -/
def IsLopsidedDependency (p : Ω → ℝ) (N : ι → Finset ι) : Prop :=
  ∀ i (T : Finset ι), Disjoint T (N i) → i ∉ T →
    prob p (A i ∩ avoid A T) ≤ prob p (A i) * prob p (avoid A T)

variable [DecidableEq ι]

lemma avoid_insert (a : ι) (T : Finset ι) : avoid A (insert a T) = avoid A T \ A a := by
  ext ω
  simp only [mem_avoid, Finset.forall_mem_insert, Finset.mem_sdiff]
  exact and_comm

lemma prob_avoid_insert (p : Ω → ℝ) (a : ι) (T : Finset ι) :
    prob p (avoid A (insert a T)) = prob p (avoid A T) - prob p (A a ∩ avoid A T) := by
  rw [avoid_insert]
  have h := Finset.sum_union (f := p) (Finset.disjoint_sdiff_inter (avoid A T) (A a))
  rw [Finset.sdiff_union_inter] at h
  rw [Finset.inter_comm]
  simp only [prob]
  linarith

end Avoid

section LLL

variable {ι Ω : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {A : ι → Finset Ω}
  {p : Ω → ℝ} {x : ι → ℝ}

/-- Peeling: if each `j ∈ S` satisfies `P(A j ∩ avoid W) ≤ x j P(avoid W)` for the sets `W`
between `U` and `U ∪ S` missing `j`, then `P(avoid (U ∪ S)) ≥ ∏_{S} (1 - x) P(avoid U)`. -/
theorem prod_mul_prob_avoid_le (hx1 : ∀ i, x i ≤ 1) {U S : Finset ι} (hUS : Disjoint U S)
    (hS : ∀ j ∈ S, ∀ W, U ⊆ W → W ⊆ U ∪ S → j ∉ W →
      prob p (A j ∩ avoid A W) ≤ x j * prob p (avoid A W)) :
    (∏ j ∈ S, (1 - x j)) * prob p (avoid A U) ≤ prob p (avoid A (U ∪ S)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.disjoint_insert_right] at hUS
    have ih' := ih hUS.2 fun j hj W hUW hWS hjW =>
      hS j (Finset.mem_insert_of_mem hj) W hUW
        (hWS.trans (Finset.union_subset_union_right (Finset.subset_insert a S))) hjW
    have haW : a ∉ U ∪ S := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hUS.1, ha⟩
    have h1 := hS a (Finset.mem_insert_self a S) (U ∪ S) Finset.subset_union_left
      (Finset.union_subset_union_right (Finset.subset_insert a S)) haW
    rw [Finset.prod_insert ha, Finset.union_insert, prob_avoid_insert]
    have h0 : 0 ≤ 1 - x a := sub_nonneg.2 (hx1 a)
    have h2 := mul_le_mul_of_nonneg_left ih' h0
    nlinarith

/-- The conditional form of the **Lovász Local Lemma**: `P(A i ∩ avoid T) ≤ x i P(avoid T)`
for every `T` missing `i`. -/
theorem prob_inter_avoid_le (hp : ∀ ω, 0 ≤ p ω) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hA : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (i : ι) (T : Finset ι)
    (hiT : i ∉ T) : prob p (A i ∩ avoid A T) ≤ x i * prob p (avoid A T) := by
  induction T using Finset.strongInduction generalizing i with
  | H T ih =>
  have hdisj : Disjoint (T \ N i) (T ∩ N i) := Finset.disjoint_sdiff_inter T (N i)
  have hpeel := prod_mul_prob_avoid_le (A := A) (p := p) hx1 hdisj fun j hj W hUW hWS hjW => by
    have hWT : W ⊆ T := hWS.trans (by rw [Finset.sdiff_union_inter])
    have hWne : W ≠ T := fun h => hjW (h ▸ (Finset.mem_inter.1 hj).1)
    exact ih W (Finset.ssubset_iff_subset_ne.2 ⟨hWT, hWne⟩) j hjW
  rw [Finset.sdiff_union_inter] at hpeel
  have hprod : ∏ j ∈ N i, (1 - x j) ≤ ∏ j ∈ T ∩ N i, (1 - x j) := by
    rw [← Finset.prod_sdiff (Finset.inter_subset_right (s₁ := T))]
    exact mul_le_of_le_one_left
      (Finset.prod_nonneg fun j _ => sub_nonneg.2 (hx1 j))
      (Finset.prod_le_one₀ (fun j _ => sub_nonneg.2 (hx1 j))
        fun j _ => sub_le_self _ (hx0 j))
  have hU : Disjoint (T \ N i) (N i) := Finset.sdiff_disjoint
  have hiU : i ∉ T \ N i := fun h => hiT (Finset.mem_sdiff.1 h).1
  have hQ := prob_nonneg hp (avoid A (T \ N i))
  calc prob p (A i ∩ avoid A T) ≤ prob p (A i ∩ avoid A (T \ N i)) :=
        prob_mono hp (Finset.inter_subset_inter le_rfl (avoid_anti A Finset.sdiff_subset))
    _ ≤ prob p (A i) * prob p (avoid A (T \ N i)) := hdep i _ hU hiU
    _ ≤ x i * (∏ j ∈ T ∩ N i, (1 - x j)) * prob p (avoid A (T \ N i)) := by
        refine mul_le_mul_of_nonneg_right ((hA i).trans ?_) hQ
        exact mul_le_mul_of_nonneg_left hprod (hx0 i)
    _ ≤ x i * prob p (avoid A T) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hpeel (hx0 i)

/-- The asymmetric **Lovász Local Lemma** (lopsided form): if `0 ≤ x i ≤ 1` and
`P(A i) ≤ x i ∏_{j ∈ N i} (1 - x j)`, then `P(avoid T) ≥ ∏_{i ∈ T} (1 - x i)`. -/
theorem prod_le_prob_avoid (hp : IsDistribution p) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hA : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (T : Finset ι) :
    ∏ i ∈ T, (1 - x i) ≤ prob p (avoid A T) := by
  have h := prod_mul_prob_avoid_le (A := A) (p := p) hx1 (Finset.disjoint_empty_left T)
    fun j _ W _ _ hjW => prob_inter_avoid_le hp.nonneg hdep hx0 hx1 hA j W hjW
  rwa [avoid_empty, prob_univ hp, mul_one, Finset.empty_union] at h

/-- With `x i < 1` the events are avoided simultaneously with positive weight. -/
theorem prob_avoid_pos (hp : IsDistribution p) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hA : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (T : Finset ι) :
    0 < prob p (avoid A T) :=
  (Finset.prod_pos fun i _ => sub_pos.2 (hx1 i)).trans_le
    (prod_le_prob_avoid hp hdep hx0 (fun i => (hx1 i).le) hA T)

/-- Under the hypotheses of the Local Lemma some outcome lies in none of the `A i`, `i ∈ T`. -/
theorem exists_forall_not_mem_of_lll (hp : IsDistribution p) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hA : ∀ i, prob p (A i) ≤ x i * ∏ j ∈ N i, (1 - x j)) (T : Finset ι) :
    ∃ ω, ∀ i ∈ T, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := Finset.nonempty_of_sum_ne_zero (prob_avoid_pos hp hdep hx0 hx1 hA T).ne'
  exact ⟨ω, (mem_avoid A).1 hω⟩

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] in
/-- `exp (-1) ≤ (1 - 1/(d+1))^d`, the estimate behind the symmetric Local Lemma. -/
theorem exp_neg_one_le_one_sub_inv_pow (d : ℕ) :
    Real.exp (-1) ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [pow_zero, Real.exp_le_one_iff]
    norm_num
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  have hy : 1 - 1 / ((d : ℝ) + 1) = d / (d + 1) := by
    field_simp
    ring
  have hpos : 0 < 1 - 1 / ((d : ℝ) + 1) := by rw [hy]; positivity
  have hinv : (1 - 1 / ((d : ℝ) + 1))⁻¹ = 1 + 1 / d := by
    rw [hy, inv_div]
    field_simp
  have hlog : Real.log (1 + 1 / d) ≤ 1 / d := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / d by positivity)
    linarith
  have hl : Real.log (1 - 1 / ((d : ℝ) + 1)) = -Real.log (1 + 1 / d) := by
    rw [← hinv, Real.log_inv, neg_neg]
  have hdd : (d : ℝ) * (1 / d) = 1 := by field_simp
  have key : -1 ≤ (d : ℝ) * Real.log (1 - 1 / ((d : ℝ) + 1)) := by
    rw [hl]
    nlinarith
  calc Real.exp (-1) ≤ Real.exp ((d : ℝ) * Real.log (1 - 1 / ((d : ℝ) + 1))) :=
        Real.exp_le_exp.2 key
    _ = (1 - 1 / ((d : ℝ) + 1)) ^ d := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hpos d)]

/-- The **symmetric Lovász Local Lemma**: if `P(A i) ≤ q`, `|N i| ≤ d` and `e q (d + 1) ≤ 1`,
then the events are avoided simultaneously with positive weight. -/
theorem prob_avoid_pos_of_symmetric (hp : IsDistribution p) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) {q : ℝ} {d : ℕ} (hq : ∀ i, prob p (A i) ≤ q)
    (hN : ∀ i, (N i).card ≤ d) (hqd : Real.exp 1 * q * (d + 1) ≤ 1) (T : Finset ι) :
    0 < prob p (avoid A T) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hq' : q ≤ Real.exp (-1) / (d + 1) := by
    rw [le_div_iff₀ (by positivity), Real.exp_neg, ← one_div, le_div_iff₀ he]
    linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hN0 : ∀ i, N i = ∅ := fun i => Finset.card_eq_zero.1 (Nat.le_zero.1 (hN i))
    refine prob_avoid_pos (x := fun _ => 1 / 2) hp hdep (fun _ => by norm_num)
      (fun _ => by norm_num) (fun i => ?_) T
    rw [hN0 i, Finset.prod_empty, mul_one]
    refine (hq i).trans (hq'.trans ?_)
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [Real.exp_neg, Nat.cast_zero, zero_add, div_one]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num; linarith)
  have hd1 : (1 : ℝ) ≤ d := Nat.one_le_cast.2 hd
  have hx0 : (0 : ℝ) ≤ 1 / ((d : ℝ) + 1) := by positivity
  have hx1 : 1 / ((d : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  refine prob_avoid_pos (x := fun _ => 1 / ((d : ℝ) + 1)) hp hdep (fun _ => hx0)
    (fun _ => hx1) (fun i => ?_) T
  rw [Finset.prod_const]
  have hpow : (1 - 1 / ((d : ℝ) + 1)) ^ d ≤ (1 - 1 / ((d : ℝ) + 1)) ^ (N i).card :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (hN i)
  calc prob p (A i) ≤ Real.exp (-1) / (d + 1) := (hq i).trans hq'
    _ = 1 / ((d : ℝ) + 1) * Real.exp (-1) := by ring
    _ ≤ 1 / ((d : ℝ) + 1) * (1 - 1 / ((d : ℝ) + 1)) ^ (N i).card :=
        mul_le_mul_of_nonneg_left ((exp_neg_one_le_one_sub_inv_pow d).trans hpow) hx0

/-- The symmetric Local Lemma in existence form: some outcome lies in none of the `A i`. -/
theorem exists_forall_not_mem_of_symmetric (hp : IsDistribution p) {N : ι → Finset ι}
    (hdep : IsLopsidedDependency A p N) {q : ℝ} {d : ℕ} (hq : ∀ i, prob p (A i) ≤ q)
    (hN : ∀ i, (N i).card ≤ d) (hqd : Real.exp 1 * q * (d + 1) ≤ 1) (T : Finset ι) :
    ∃ ω, ∀ i ∈ T, ω ∉ A i := by
  obtain ⟨ω, hω⟩ := Finset.nonempty_of_sum_ne_zero
    (prob_avoid_pos_of_symmetric hp hdep hq hN hqd T).ne'
  exact ⟨ω, (mem_avoid A).1 hω⟩

end LLL

section ProductMeasure

/-- The product weight of `ω : κ → α` with independent coordinates of law `μ`. -/
def productWeight {κ α : Type*} [Fintype κ] (μ : α → ℝ) (ω : κ → α) : ℝ := ∏ k, μ (ω k)

/-- The event `A` only reads the coordinates in `V`. -/
def DependsOn {κ α : Type*} (A : Finset (κ → α)) (V : Finset κ) : Prop :=
  ∀ ω ω' : κ → α, (∀ k ∈ V, ω k = ω' k) → (ω ∈ A ↔ ω' ∈ A)

/-- Coordinates in `V` from `ω`, the rest from `ω'`. -/
def hybrid {κ α : Type*} [DecidableEq κ] (V : Finset κ) (ω ω' : κ → α) : κ → α :=
  fun k => if k ∈ V then ω k else ω' k

variable {κ α : Type*} [Fintype κ] [DecidableEq κ] [Fintype α] [DecidableEq α]

omit [Fintype κ] [Fintype α] [DecidableEq α] in
@[simp] lemma hybrid_hybrid (V : Finset κ) (ω ω' : κ → α) :
    hybrid V (hybrid V ω ω') (hybrid V ω' ω) = ω := by
  funext k
  by_cases hk : k ∈ V <;> simp [hybrid, hk]

omit [Fintype α] [DecidableEq α] in
lemma productWeight_hybrid_mul (μ : α → ℝ) (V : Finset κ) (ω ω' : κ → α) :
    productWeight μ (hybrid V ω ω') * productWeight μ (hybrid V ω' ω) =
      productWeight μ ω * productWeight μ ω' := by
  simp only [productWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ V
  · simp only [hybrid, hk, ↓reduceIte]
  · simp only [hybrid, hk, ↓reduceIte]
    exact mul_comm _ _

omit [DecidableEq α] in
lemma sum_productWeight {μ : α → ℝ} (hμ : ∑ a, μ a = 1) :
    ∑ ω : κ → α, productWeight μ ω = 1 := by
  have h := Finset.prod_univ_sum (fun _ : κ => (Finset.univ : Finset α)) fun _ a => μ a
  simp only [hμ, Finset.prod_const_one, Fintype.piFinset_univ] at h
  exact h.symm

omit [DecidableEq α] in
lemma isDistribution_productWeight {μ : α → ℝ} (hμ : IsDistribution μ) :
    IsDistribution (productWeight (κ := κ) μ) where
  nonneg ω := Finset.prod_nonneg fun k _ => hμ.nonneg (ω k)
  sum_eq_one := sum_productWeight hμ.sum_eq_one

/-- **Independence under a product measure**: events reading disjoint coordinate sets `V` and
`Vᶜ` are independent. -/
theorem prob_inter_eq_mul_of_dependsOn {μ : α → ℝ} (hμ : ∑ a, μ a = 1)
    {A B : Finset (κ → α)} {V : Finset κ} (hA : DependsOn A V) (hB : DependsOn B Vᶜ) :
    prob (productWeight μ) (A ∩ B) = prob (productWeight μ) A * prob (productWeight μ) B := by
  have hAh : ∀ ω ω' : κ → α, hybrid V ω ω' ∈ A ↔ ω ∈ A := fun ω ω' =>
    hA _ _ fun k hk => by simp [hybrid, hk]
  have hBh : ∀ ω ω' : κ → α, hybrid V ω' ω ∈ B ↔ ω ∈ B := fun ω ω' =>
    hB _ _ fun k hk => by simp [hybrid, Finset.mem_compl.1 hk]
  have hR : prob (productWeight μ) A * prob (productWeight μ) B =
      ∑ x : (κ → α) × (κ → α), if x.1 ∈ A ∧ x.2 ∈ B then
        productWeight μ x.1 * productWeight μ x.2 else 0 := by
    rw [Fintype.sum_prod_type, prob, prob, Finset.sum_mul_sum, ← Fintype.sum_ite_mem A]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ A
    · simp only [ha, true_and, ↓reduceIte]
      exact (Fintype.sum_ite_mem B _).symm
    · simp [ha]
  have hL : prob (productWeight μ) (A ∩ B) =
      ∑ x : (κ → α) × (κ → α), if x.1 ∈ A ∩ B then
        productWeight μ x.1 * productWeight μ x.2 else 0 := by
    rw [Fintype.sum_prod_type, prob, ← Fintype.sum_ite_mem (A ∩ B)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a ∈ A ∩ B
    · simp only [ha, ↓reduceIte]
      rw [← Finset.mul_sum, sum_productWeight hμ, mul_one]
    · simp only [ha, ↓reduceIte, Finset.sum_const_zero]
  have hinv : Function.Involutive fun x : (κ → α) × (κ → α) =>
      (hybrid V x.1 x.2, hybrid V x.2 x.1) := fun x => by simp
  rw [hL, hR]
  refine Eq.trans ?_ (hinv.bijective.sum_comp fun x : (κ → α) × (κ → α) =>
    if x.1 ∈ A ∧ x.2 ∈ B then productWeight μ x.1 * productWeight μ x.2 else 0)
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [hAh, hBh, productWeight_hybrid_mul, Finset.mem_inter]

/-- Events with variable sets `vbl i` under a product measure are lopsidedly dependent on any
`N` that contains every `j ≠ i` whose variables meet `vbl i`. -/
theorem isLopsidedDependency_of_dependsOn {ι : Type*} {μ : α → ℝ} (hμ : ∑ a, μ a = 1)
    {A : ι → Finset (κ → α)} {vbl : ι → Finset κ} (hA : ∀ i, DependsOn (A i) (vbl i))
    {N : ι → Finset ι} (hN : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ N i) :
    IsLopsidedDependency A (productWeight μ) N := by
  intro i T hT hiT
  refine (prob_inter_eq_mul_of_dependsOn hμ (hA i) ?_).le
  intro ω ω' h
  have key : ∀ j ∈ T, (ω ∉ A j ↔ ω' ∉ A j) := fun j hj => by
    have hji : j ≠ i := fun e => hiT (e ▸ hj)
    have hjN : j ∉ N i := Finset.disjoint_left.1 hT hj
    have hdisj : Disjoint (vbl i) (vbl j) := by
      by_contra hc
      exact hjN (hN i j hji hc)
    exact not_congr (hA j ω ω' fun k hk =>
      h k (Finset.mem_compl.2 (Finset.disjoint_right.1 hdisj hk)))
  simp only [mem_avoid]
  exact ⟨fun H j hj => (key j hj).1 (H j hj), fun H j hj => (key j hj).2 (H j hj)⟩

/-- A cylinder event fixing the coordinates in `V` to `a` has weight `∏_{k ∈ V} μ (a k)`. -/
theorem prob_cylinder {μ : α → ℝ} (hμ : ∑ b, μ b = 1) (V : Finset κ) (a : κ → α)
    [DecidablePred fun ω : κ → α => ∀ k ∈ V, ω k = a k] :
    prob (productWeight μ) ({ω | ∀ k ∈ V, ω k = a k} : Finset (κ → α)) =
      ∏ k ∈ V, μ (a k) := by
  have hpt : ∀ ω : κ → α, (if ∀ k ∈ V, ω k = a k then productWeight μ ω else 0) =
      ∏ k, (if k ∈ V then (if ω k = a k then μ (ω k) else 0) else μ (ω k)) := fun ω => by
    unfold productWeight
    by_cases h : ∀ k ∈ V, ω k = a k
    · rw [ite_eq_left h]
      refine Finset.prod_congr rfl fun k _ => ?_
      by_cases hk : k ∈ V
      · rw [ite_eq_left hk, ite_eq_left (h k hk)]
      · rw [ite_eq_right hk]
    · rw [ite_eq_right h]
      obtain ⟨k, hk, hne⟩ : ∃ k ∈ V, ω k ≠ a k := by
        by_contra hc
        exact h fun k hk => by_contra fun hne => hc ⟨k, hk, hne⟩
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      rw [ite_eq_left hk, ite_eq_right hne]
  have hfac := (Finset.prod_univ_sum (fun _ : κ => (Finset.univ : Finset α))
    fun k b => if k ∈ V then (if b = a k then μ b else 0) else μ b).symm
  rw [Fintype.piFinset_univ] at hfac
  rw [prob, Finset.sum_filter, Finset.sum_congr rfl fun ω _ => hpt ω, hfac,
    ← Fintype.prod_ite_mem V]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k ∈ V
  · simp only [hk, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ]
  · simp only [hk, ↓reduceIte, hμ]

end ProductMeasure

end

end TheoremOS.Probability
