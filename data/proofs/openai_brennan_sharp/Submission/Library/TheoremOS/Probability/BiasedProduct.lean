import Submission.Library.TheoremOS.Probability.FiniteProbability

/-!
# The `p`-biased product measure on subsets of a finite set

`biasedMass p s = ∏ x, if x ∈ s then p else 1 - p` is the probability that a random subset of the
finite type `α`, containing each element independently with probability `p`, equals `s`. Contents:
the power form `p ^ |s| * (1 - p) ^ |univ \ s|`, complements, nonnegativity, the independence
identity `∑ s, μ_p(s) (∏_{x ∈ s} f x) (∏_{x ∉ s} g x) = ∏ x, (p f x + (1 - p) g x)`, total mass
one, the probabilities `p ^ |t|` of containing `t` and `(1 - p) ^ |t|` of avoiding it, the expected
size, the union bound over a cover by generators, the endpoint values `p = 0, 1`, continuity in
`p`; the lattice condition between `μ_p` and `μ_q`, monotonicity of `μ_p` on increasing families
and of `E_p[F]` for monotone `F` (Holley), and the Harris (FKG) inequality; the Russo–Margulis
formula `d/dp E_p[F] = ∑ x, E_p[F (s ∪ {x}) - F (s \ {x})]` and, for an increasing family, `d/dp
μ_p(A) = ∑ x, μ_p(x is pivotal)`; the same statements for configurations `x : α → Bool`.

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Section 8.4 (`p`-biased measures); N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed.,
Wiley, 2016, Chapter 6 (the FKG and Harris inequalities); G. Grimmett, *Percolation*, 2nd ed.,
Springer, 1999, Sections 2.1–2.4 (monotone coupling, increasing events, Russo's formula).
Textbook material; nothing here is specific to a benchmark problem.

Bridges: a weight `∏ x, if x ∈ W then p else 1 - p` is `biasedMass p W` by `rfl`; a weight
`p ^ s.card * (1 - p) ^ (univ \ s).card` is `biasedMass p s` by `biasedMass_eq_pow_mul_pow`; a
family probability `∑ s ∈ D, …` is `∑ s ∈ D, biasedMass p s`. A cover `∀ S ∈ A, ∃ I ∈ G, I ⊆ S`
gives `∑ s ∈ A, biasedMass p s ≤ ∑ I ∈ G, p ^ I.card` (`sum_biasedMass_le_of_covers`). For a
configuration weight `∏ e, if x e = true then p else 1 - p` use `biasedWeight`, and turn an
"increasing" hypothesis `∀ x y, (∀ e, x e = true → y e = true) → f x = true → f y = true` into
`Monotone` with `monotone_indicator_of_increasing`. Mathlib's `fkg` and `holley` are stated for any
finite distributive lattice; here they are specialised to `Finset α` with the product weights.
-/

namespace TheoremOS.Probability

open Finset
open TheoremOS.InformationTheory

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased product weight of `s`: each element present independently with probability
`p`. -/
def biasedMass (p : ℝ) (s : Finset α) : ℝ := ∏ x, if x ∈ s then p else 1 - p

section Basic

variable {p : ℝ}

theorem biasedMass_eq_prod_mul_prod (p : ℝ) (s : Finset α) :
    biasedMass p s = (∏ _x ∈ s, p) * ∏ _x ∈ sᶜ, (1 - p) := by
  rw [biasedMass, ← Finset.prod_mul_prod_compl s]
  congr 1 <;> refine Finset.prod_congr rfl fun x hx => ?_
  · simp [hx]
  · simp [Finset.mem_compl.mp hx]

/-- The power form `p ^ |s| * (1 - p) ^ |univ \ s|`. -/
theorem biasedMass_eq_pow_mul_pow (p : ℝ) (s : Finset α) :
    biasedMass p s = p ^ s.card * (1 - p) ^ (univ \ s).card := by
  rw [biasedMass_eq_prod_mul_prod, prod_const, prod_const, compl_eq_univ_sdiff]

theorem biasedMass_compl (p : ℝ) (s : Finset α) : biasedMass p sᶜ = biasedMass (1 - p) s := by
  unfold biasedMass
  refine Finset.prod_congr rfl fun x _ => ?_
  by_cases hx : x ∈ s <;> simp [hx]

theorem biasedMass_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : Finset α) : 0 ≤ biasedMass p s :=
  Finset.prod_nonneg fun x _ => by split_ifs <;> linarith

/-- Independence: `∑ s, μ_p(s) (∏_{x ∈ s} f x) (∏_{x ∉ s} g x) = ∏ x, (p f x + (1 - p) g x)`. -/
theorem sum_biasedMass_mul_prod_mul_prod (p : ℝ) (f g : α → ℝ) :
    ∑ s, biasedMass p s * ((∏ x ∈ s, f x) * ∏ x ∈ sᶜ, g x) =
      ∏ x, (p * f x + (1 - p) * g x) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [biasedMass_eq_prod_mul_prod, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

theorem sum_biasedMass (p : ℝ) : ∑ s : Finset α, biasedMass p s = 1 := by
  simpa using sum_biasedMass_mul_prod_mul_prod (α := α) p (fun _ => 1) (fun _ => 1)

theorem isDistribution_biasedMass (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsDistribution (biasedMass (α := α) p) :=
  ⟨biasedMass_nonneg hp₀ hp₁, sum_biasedMass p⟩

/-- The probability of containing `t` is `p ^ |t|`. -/
theorem sum_biasedMass_superset (p : ℝ) (t : Finset α) :
    ∑ s with t ⊆ s, biasedMass p s = p ^ t.card := by
  have h := sum_biasedMass_mul_prod_mul_prod p (fun _ => 1) (fun x => if x ∈ t then 0 else 1)
  have hl : ∀ s : Finset α, ((∏ x ∈ s, (1 : ℝ)) * ∏ x ∈ sᶜ, if x ∈ t then (0 : ℝ) else 1) =
      if t ⊆ s then 1 else 0 := by
    intro s
    rw [prod_const_one, one_mul]
    split_ifs with hts
    · exact Finset.prod_eq_one fun x hx => by
        simp [show x ∉ t from fun hxt => Finset.mem_compl.mp hx (hts hxt)]
    · obtain ⟨x, hxt, hxs⟩ := Finset.not_subset.mp hts
      exact Finset.prod_eq_zero (Finset.mem_compl.mpr hxs) (by simp [hxt])
  have hr : ∏ x, (p * 1 + (1 - p) * if x ∈ t then (0 : ℝ) else 1) = p ^ t.card := by
    rw [← Finset.prod_mul_prod_compl t]
    have h1 : ∏ x ∈ t, (p * 1 + (1 - p) * if x ∈ t then (0 : ℝ) else 1) = ∏ _x ∈ t, p :=
      Finset.prod_congr rfl fun x hx => by simp [hx]
    have h2 : ∏ x ∈ tᶜ, (p * 1 + (1 - p) * if x ∈ t then (0 : ℝ) else 1) = 1 :=
      Finset.prod_eq_one fun x hx => by simp [Finset.mem_compl.mp hx]
    rw [h1, h2, prod_const, mul_one]
  rw [hr] at h
  simp only [hl, mul_ite, mul_one, mul_zero] at h
  rw [Finset.sum_filter, h]

theorem sum_biasedMass_mem (p : ℝ) (a : α) : ∑ s with a ∈ s, biasedMass p s = p := by
  simpa using sum_biasedMass_superset p {a}

/-- The probability of avoiding `t` is `(1 - p) ^ |t|`. -/
theorem sum_biasedMass_disjoint (p : ℝ) (t : Finset α) :
    ∑ s with Disjoint s t, biasedMass p s = (1 - p) ^ t.card := by
  rw [← sum_biasedMass_superset (1 - p) t, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_equiv (Equiv.ofBijective compl compl_involutive.bijective) (g := fun s =>
    if t ⊆ s then biasedMass (1 - p) s else 0)]
  · intro s; simp
  · intro s _
    simp only [Equiv.ofBijective_apply, ← biasedMass_compl, Finset.subset_compl_iff_disjoint_left,
      disjoint_comm, compl_compl]

/-- The expected size of the random subset is `p |α|`. -/
theorem sum_biasedMass_mul_card (p : ℝ) :
    ∑ s : Finset α, biasedMass p s * s.card = p * Fintype.card α := by
  have : ∀ s : Finset α, (s.card : ℝ) = ∑ a : α, if a ∈ s then 1 else 0 := by
    intro s; simp
  simp_rw [this, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_filter, sum_biasedMass_mem]
  simp [Finset.card_univ, mul_comm]

/-- The union bound over generators: if every member of `A` contains a member of `G`, then
`μ_p(A) ≤ ∑_{I ∈ G} p ^ |I|`. -/
theorem sum_biasedMass_le_of_covers {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {A G : Finset (Finset α)}
    (hcov : ∀ s ∈ A, ∃ I ∈ G, I ⊆ s) : ∑ s ∈ A, biasedMass p s ≤ ∑ I ∈ G, p ^ I.card := by
  calc ∑ s ∈ A, biasedMass p s
      ≤ ∑ s ∈ A, ∑ I ∈ G, if I ⊆ s then biasedMass p s else 0 := by
        refine Finset.sum_le_sum fun s hs => ?_
        obtain ⟨I, hI, hIs⟩ := hcov s hs
        refine le_trans ?_ (Finset.single_le_sum (f := fun I => if I ⊆ s then biasedMass p s else 0)
          (fun J _ => by split_ifs <;> simp [biasedMass_nonneg hp₀ hp₁]) hI)
        simp [hIs]
    _ ≤ ∑ s, ∑ I ∈ G, if I ⊆ s then biasedMass p s else 0 :=
        Finset.sum_le_univ_sum_of_nonneg fun s => Finset.sum_nonneg fun I _ => by
          split_ifs <;> simp [biasedMass_nonneg hp₀ hp₁]
    _ = ∑ I ∈ G, p ^ I.card := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => by rw [← Finset.sum_filter, sum_biasedMass_superset]

theorem biasedMass_zero (s : Finset α) : biasedMass 0 s = if s = ∅ then 1 else 0 := by
  rw [biasedMass_eq_pow_mul_pow]
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · simp [hs.ne_empty, zero_pow (Finset.card_pos.mpr hs).ne']

theorem biasedMass_one (s : Finset α) : biasedMass 1 s = if s = univ then 1 else 0 := by
  have h := biasedMass_compl 1 sᶜ
  rw [compl_compl, sub_self] at h
  rw [h, biasedMass_zero]
  simp [compl_eq_empty_iff]

theorem continuous_biasedMass (s : Finset α) : Continuous fun p => biasedMass p s := by
  unfold biasedMass
  exact continuous_finsetProd _ fun x _ => by split_ifs <;> fun_prop

end Basic

section Correlation

variable {p q : ℝ}

/-- The lattice condition between `μ_p` and `μ_q` for `p ≤ q`:
`μ_p(s) μ_q(t) ≤ μ_p(s ∩ t) μ_q(s ∪ t)`. For `p = q` it is an equality. -/
theorem biasedMass_mul_le (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1) (s t : Finset α) :
    biasedMass p s * biasedMass q t ≤ biasedMass p (s ∩ t) * biasedMass q (s ∪ t) := by
  unfold biasedMass
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun x _ => by split_ifs <;> nlinarith) fun x _ => ?_
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [hs, ht]
  all_goals nlinarith

/-- Holley: for `p ≤ q` and monotone `F`, `E_p[F] ≤ E_q[F]`. -/
theorem sum_biasedMass_mul_le_of_monotone (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1)
    {F : Finset α → ℝ} (hF : Monotone F) :
    ∑ s, biasedMass p s * F s ≤ ∑ s, biasedMass q s * F s := by
  have hp₁ : p ≤ 1 := hpq.trans hq₁
  have hq₀ : 0 ≤ q := hp₀.trans hpq
  have key := holley (biasedMass p) (biasedMass q) (fun s => F s - F ∅)
    (fun s => sub_nonneg.mpr (hF (Finset.empty_subset s)))
    (fun s => biasedMass_nonneg hp₀ hp₁ s) (fun s => biasedMass_nonneg hq₀ hq₁ s)
    (fun s t hst => sub_le_sub_right (hF hst) _)
    (by rw [sum_biasedMass, sum_biasedMass])
    (fun s t => biasedMass_mul_le hp₀ hpq hq₁ s t)
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_biasedMass, one_mul,
    mul_comm (F _ - F ∅)] at key
  simp only [mul_comm (biasedMass _ _)] at key ⊢
  linarith [key]

/-- Monotonicity in `p` of the probability of an increasing family. -/
theorem sum_biasedMass_le_of_isUpperSet (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1)
    {A : Finset (Finset α)} (hA : ∀ s ∈ A, ∀ t, s ⊆ t → t ∈ A) :
    ∑ s ∈ A, biasedMass p s ≤ ∑ s ∈ A, biasedMass q s := by
  have hF : Monotone fun s => if s ∈ A then (1 : ℝ) else 0 := by
    intro s t hst
    by_cases hs : s ∈ A
    · simp [hs, hA s hs t hst]
    · simp only [hs, ite_false]; split_ifs <;> norm_num
  have := sum_biasedMass_mul_le_of_monotone hp₀ hpq hq₁ hF
  simpa [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter] using this

/-- The Harris (FKG) inequality: increasing functions are positively correlated under `μ_p`. -/
theorem harris {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {F G : Finset α → ℝ} (hF : Monotone F)
    (hG : Monotone G) :
    (∑ s, biasedMass p s * F s) * (∑ s, biasedMass p s * G s) ≤
      ∑ s, biasedMass p s * (F s * G s) := by
  have key := fkg (fun s => F s - F ∅) (fun s => G s - G ∅) (biasedMass p)
    (fun s => biasedMass_nonneg hp₀ hp₁ s) (fun s => sub_nonneg.mpr (hF (Finset.empty_subset s)))
    (fun s => sub_nonneg.mpr (hG (Finset.empty_subset s)))
    (fun s t hst => sub_le_sub_right (hF hst) _) (fun s t hst => sub_le_sub_right (hG hst) _)
    (fun s t => biasedMass_mul_le hp₀ le_rfl hp₁ s t)
  rw [sum_biasedMass, one_mul] at key
  have e1 : ∑ s, biasedMass p s * (F s - F ∅) = (∑ s, biasedMass p s * F s) - F ∅ := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_biasedMass]
  have e2 : ∑ s, biasedMass p s * (G s - G ∅) = (∑ s, biasedMass p s * G s) - G ∅ := by
    simp [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_biasedMass]
  have e3 : ∑ s, biasedMass p s * ((F s - F ∅) * (G s - G ∅)) =
      ∑ s, biasedMass p s * (F s * G s) - G ∅ * ∑ s, biasedMass p s * F s -
        F ∅ * ∑ s, biasedMass p s * G s + F ∅ * G ∅ := by
    have h : ∀ s, biasedMass p s * ((F s - F ∅) * (G s - G ∅)) =
        biasedMass p s * (F s * G s) - G ∅ * (biasedMass p s * F s) -
          F ∅ * (biasedMass p s * G s) + F ∅ * G ∅ * biasedMass p s := fun s => by ring
    simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_biasedMass,
      mul_one]
  rw [e1, e2, e3] at key
  nlinarith [key]

/-- Harris for increasing families: `μ_p(A) μ_p(B) ≤ μ_p(A ∩ B)`. -/
theorem sum_biasedMass_mul_le_inter {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {A B : Finset (Finset α)} (hA : ∀ s ∈ A, ∀ t, s ⊆ t → t ∈ A)
    (hB : ∀ s ∈ B, ∀ t, s ⊆ t → t ∈ B) :
    (∑ s ∈ A, biasedMass p s) * (∑ s ∈ B, biasedMass p s) ≤ ∑ s ∈ A ∩ B, biasedMass p s := by
  have mono : ∀ C : Finset (Finset α), (∀ s ∈ C, ∀ t, s ⊆ t → t ∈ C) →
      Monotone fun s => if s ∈ C then (1 : ℝ) else 0 := by
    intro C hC s t hst
    by_cases hs : s ∈ C
    · simp [hs, hC s hs t hst]
    · simp only [hs, ite_false]; split_ifs <;> norm_num
  have := harris hp₀ hp₁ (mono A hA) (mono B hB)
  simp only [mul_ite, mul_one, mul_zero] at this
  rw [Finset.inter_comm]
  simpa [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.mem_inter, ite_and] using this

end Correlation

section Russo

/-- Pairing the subsets of `α` by the presence of `x`. -/
theorem sum_eq_sum_powerset_erase {M : Type*} [AddCommMonoid M] (x : α) (G : Finset α → M) :
    ∑ s, G s = ∑ t ∈ (univ.erase x).powerset, (G t + G (insert x t)) := by
  rw [Finset.sum_add_distrib, ← Finset.sum_powerset_insert (Finset.notMem_erase x univ),
    Finset.insert_erase (Finset.mem_univ x), Finset.powerset_univ]

/-- Splitting off the factor at `x`. -/
theorem biasedMass_eq_mul_prod_erase (p : ℝ) (x : α) (s : Finset α) :
    biasedMass p s = (if x ∈ s then p else 1 - p) *
      ∏ y ∈ univ.erase x, if y ∈ s then p else 1 - p :=
  (Finset.mul_prod_erase univ (fun y => if y ∈ s then p else 1 - p) (Finset.mem_univ x)).symm

omit [Fintype α] in
theorem prod_erase_ite_insert {s : Finset α} (p : ℝ) (x : α) (t : Finset α) :
    ∏ y ∈ s.erase x, (if y ∈ insert x t then p else 1 - p) =
      ∏ y ∈ s.erase x, if y ∈ t then p else 1 - p :=
  Finset.prod_congr rfl fun y hy => by simp [Finset.mem_insert, Finset.ne_of_mem_erase hy]

/-- The derivative of `μ_p(s)` in direction `x`, summed against `F`, is the expected discrete
derivative `F (s ∪ {x}) - F (s \ {x})`. -/
theorem sum_ite_mul_prod_erase_mul (p : ℝ) (x : α) (F : Finset α → ℝ) :
    ∑ s, (if x ∈ s then (1 : ℝ) else -1) * (∏ y ∈ univ.erase x, if y ∈ s then p else 1 - p) * F s =
      ∑ s, biasedMass p s * (F (insert x s) - F (s.erase x)) := by
  conv_lhs => rw [sum_eq_sum_powerset_erase x]
  conv_rhs => rw [sum_eq_sum_powerset_erase x]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hxt : x ∉ t := fun h => Finset.notMem_erase x univ (Finset.mem_powerset.mp ht h)
  rw [biasedMass_eq_mul_prod_erase p x t, biasedMass_eq_mul_prod_erase p x (insert x t),
    prod_erase_ite_insert, Finset.insert_idem, Finset.erase_insert hxt,
    Finset.erase_eq_of_notMem hxt]
  simp only [hxt, Finset.mem_insert_self, ite_true, ite_false]
  ring

/-- Russo–Margulis: `d/dp E_p[F] = ∑ x, E_p[F (s ∪ {x}) - F (s \ {x})]`. -/
theorem hasDerivAt_sum_biasedMass_mul (p : ℝ) (F : Finset α → ℝ) :
    HasDerivAt (fun q => ∑ s, biasedMass q s * F s)
      (∑ x, ∑ s, biasedMass p s * (F (insert x s) - F (s.erase x))) p := by
  have hμ : ∀ s : Finset α, HasDerivAt (fun q => biasedMass q s)
      (∑ x, (∏ y ∈ univ.erase x, if y ∈ s then p else 1 - p) *
        (if x ∈ s then (1 : ℝ) else -1)) p := by
    intro s
    have h := HasDerivAt.fun_finsetProd (u := univ) (x := p)
      (f := fun y q => if y ∈ s then q else 1 - q)
      (f' := fun y => if y ∈ s then (1 : ℝ) else -1) fun y _ => by
        by_cases hy : y ∈ s
        · simpa [hy] using hasDerivAt_id' (x := p)
        · simpa [hy] using (hasDerivAt_id' (x := p)).const_sub 1
    exact h
  have h := HasDerivAt.fun_sum (u := univ) fun s _ => (hμ s).mul_const (F s)
  convert h using 1
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← sum_ite_mul_prod_erase_mul p x F]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Russo's formula for an increasing family: `d/dp μ_p(A)` is the expected number of pivotal
elements, `∑ x, μ_p {s | s ∪ {x} ∈ A, s \ {x} ∉ A}`. -/
theorem hasDerivAt_sum_biasedMass_of_isUpperSet (p : ℝ) {A : Finset (Finset α)}
    (hA : ∀ s ∈ A, ∀ t, s ⊆ t → t ∈ A) :
    HasDerivAt (fun q => ∑ s ∈ A, biasedMass q s)
      (∑ x, ∑ s with insert x s ∈ A ∧ s.erase x ∉ A, biasedMass p s) p := by
  have h := hasDerivAt_sum_biasedMass_mul p fun s => if s ∈ A then (1 : ℝ) else 0
  convert h using 1
  · funext q
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases h1 : insert x s ∈ A <;> by_cases h2 : s.erase x ∈ A
    · simp [h1, h2]
    · simp [h1, h2]
    · exact absurd (hA _ h2 _ ((Finset.erase_subset x s).trans (Finset.subset_insert x s))) h1
    · simp [h1, h2]

end Russo

section Config

variable {p q : ℝ}

/-- The `p`-biased weight of a configuration `x : α → Bool`. -/
def biasedWeight (p : ℝ) (x : α → Bool) : ℝ := ∏ e, if x e = true then p else 1 - p

/-- The configuration with support `s`. -/
def configOf (s : Finset α) : α → Bool := fun e => decide (e ∈ s)

omit [Fintype α] in
@[simp] theorem configOf_apply (s : Finset α) (e : α) : configOf s e = decide (e ∈ s) := rfl

/-- Configurations are subsets: `x ↦ {e | x e = true}`. -/
def configEquiv : (α → Bool) ≃ Finset α where
  toFun x := univ.filter fun e => x e = true
  invFun := configOf
  left_inv x := by funext e; simp [configOf]
  right_inv s := by ext e; simp [configOf]

theorem biasedWeight_configOf (p : ℝ) (s : Finset α) :
    biasedWeight p (configOf s) = biasedMass p s := by
  simp [biasedWeight, biasedMass, configOf]

theorem biasedWeight_eq_biasedMass (p : ℝ) (x : α → Bool) :
    biasedWeight p x = biasedMass p (configEquiv x) := by
  simp [biasedWeight, biasedMass, configEquiv]

/-- Sums over configurations are sums over subsets. -/
theorem sum_biasedWeight_mul (p : ℝ) (F : (α → Bool) → ℝ) :
    ∑ x, biasedWeight p x * F x = ∑ s, biasedMass p s * F (configOf s) := by
  refine (Fintype.sum_equiv configEquiv.symm (fun s => biasedMass p s * F (configOf s)) _
    fun s => ?_).symm
  show biasedMass p s * F (configOf s) = biasedWeight p (configOf s) * F (configOf s)
  rw [biasedWeight_configOf]

theorem sum_biasedWeight (p : ℝ) : ∑ x : α → Bool, biasedWeight p x = 1 := by
  simpa [sum_biasedMass] using sum_biasedWeight_mul (α := α) p fun _ => (1 : ℝ)

theorem biasedWeight_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (x : α → Bool) :
    0 ≤ biasedWeight p x := by
  rw [biasedWeight_eq_biasedMass]; exact biasedMass_nonneg hp₀ hp₁ _

theorem isDistribution_biasedWeight (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    IsDistribution (biasedWeight (α := α) p) :=
  ⟨biasedWeight_nonneg hp₀ hp₁, sum_biasedWeight p⟩

omit [DecidableEq α] in
theorem continuous_biasedWeight (x : α → Bool) : Continuous fun p => biasedWeight p x := by
  unfold biasedWeight
  exact continuous_finsetProd _ fun e _ => by split_ifs <;> fun_prop

omit [Fintype α] in
theorem configOf_le_configOf {s t : Finset α} : configOf s ≤ configOf t ↔ s ⊆ t := by
  simp [Pi.le_def, Bool.le_iff_imp, Finset.subset_iff]

omit [Fintype α] in
theorem monotone_configOf : Monotone (configOf (α := α)) := fun _ _ h =>
  configOf_le_configOf.mpr h

omit [Fintype α] in
theorem configOf_insert (s : Finset α) (e : α) :
    configOf (insert e s) = Function.update (configOf s) e true := by
  funext y
  by_cases hy : y = e
  · subst hy; simp
  · simp [hy]

omit [Fintype α] in
theorem configOf_erase (s : Finset α) (e : α) :
    configOf (s.erase e) = Function.update (configOf s) e false := by
  funext y
  by_cases hy : y = e
  · subst hy; simp
  · simp [hy]

omit [Fintype α] in
/-- An increasing Boolean property in the "`x e = true → y e = true`" form gives a monotone
indicator on subsets. -/
theorem monotone_indicator_of_increasing {f : (α → Bool) → Bool}
    (hf : ∀ x y, (∀ e, x e = true → y e = true) → f x = true → f y = true) :
    Monotone fun s : Finset α => if f (configOf s) = true then (1 : ℝ) else 0 := by
  intro s t hst
  by_cases hs : f (configOf s) = true
  · have ht : f (configOf t) = true :=
      hf _ _ (fun e he => by simpa using hst (by simpa using he)) hs
    simp [hs, ht]
  · simp only [hs, Bool.false_eq_true, ite_false]
    split_ifs <;> norm_num

/-- `E_p[F]` is nondecreasing in `p` for monotone `F` on configurations. -/
theorem sum_biasedWeight_mul_le_of_monotone (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1)
    {F : (α → Bool) → ℝ} (hF : Monotone F) :
    ∑ x, biasedWeight p x * F x ≤ ∑ x, biasedWeight q x * F x := by
  rw [sum_biasedWeight_mul, sum_biasedWeight_mul]
  exact sum_biasedMass_mul_le_of_monotone hp₀ hpq hq₁ (hF.comp monotone_configOf)

/-- `P_p(f)` is nondecreasing in `p` for an increasing Boolean property `f`. -/
theorem sum_biasedWeight_ite_le_of_increasing (hp₀ : 0 ≤ p) (hpq : p ≤ q) (hq₁ : q ≤ 1)
    {f : (α → Bool) → Bool}
    (hf : ∀ x y, (∀ e, x e = true → y e = true) → f x = true → f y = true) :
    ∑ x, biasedWeight p x * (if f x = true then (1 : ℝ) else 0) ≤
      ∑ x, biasedWeight q x * (if f x = true then (1 : ℝ) else 0) := by
  rw [sum_biasedWeight_mul, sum_biasedWeight_mul]
  exact sum_biasedMass_mul_le_of_monotone hp₀ hpq hq₁ (monotone_indicator_of_increasing hf)

/-- The Harris inequality on configurations. -/
theorem harris_config (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {F G : (α → Bool) → ℝ} (hF : Monotone F)
    (hG : Monotone G) :
    (∑ x, biasedWeight p x * F x) * (∑ x, biasedWeight p x * G x) ≤
      ∑ x, biasedWeight p x * (F x * G x) := by
  simp only [sum_biasedWeight_mul]
  exact harris hp₀ hp₁ (hF.comp monotone_configOf) (hG.comp monotone_configOf)

/-- Harris for two increasing Boolean properties: `P_p(f) P_p(g) ≤ P_p(f ∧ g)`. -/
theorem harris_increasing (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) {f g : (α → Bool) → Bool}
    (hf : ∀ x y, (∀ e, x e = true → y e = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ e, x e = true → y e = true) → g x = true → g y = true) :
    (∑ x, biasedWeight p x * (if f x = true then (1 : ℝ) else 0)) *
        (∑ x, biasedWeight p x * (if g x = true then (1 : ℝ) else 0)) ≤
      ∑ x, biasedWeight p x * (if f x = true ∧ g x = true then (1 : ℝ) else 0) := by
  simp only [sum_biasedWeight_mul]
  refine (harris hp₀ hp₁ (monotone_indicator_of_increasing hf)
    (monotone_indicator_of_increasing hg)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h1 : f (configOf s) = true <;> by_cases h2 : g (configOf s) = true <;> simp [h1, h2]

theorem continuous_sum_biasedWeight_mul (F : (α → Bool) → ℝ) :
    Continuous fun p => ∑ x, biasedWeight p x * F x :=
  continuous_finsetSum _ fun x _ => (continuous_biasedWeight x).mul continuous_const

/-- Russo–Margulis on configurations: `d/dp E_p[F] = ∑ e, E_p[F (x[e ↦ 1]) - F (x[e ↦ 0])]`. -/
theorem hasDerivAt_sum_biasedWeight_mul (p : ℝ) (F : (α → Bool) → ℝ) :
    HasDerivAt (fun q => ∑ x, biasedWeight q x * F x)
      (∑ e, ∑ x, biasedWeight p x *
        (F (Function.update x e true) - F (Function.update x e false))) p := by
  simp only [sum_biasedWeight_mul, ← configOf_insert, ← configOf_erase]
  exact hasDerivAt_sum_biasedMass_mul p (F ∘ configOf)

/-- Russo's formula for an increasing Boolean property: `d/dp P_p(f)` is the expected number of
pivotal coordinates. -/
theorem hasDerivAt_sum_biasedWeight_ite_of_increasing (p : ℝ) {f : (α → Bool) → Bool}
    (hf : ∀ x y, (∀ e, x e = true → y e = true) → f x = true → f y = true) :
    HasDerivAt (fun q => ∑ x, biasedWeight q x * (if f x = true then (1 : ℝ) else 0))
      (∑ e, ∑ x, biasedWeight p x *
        (if f (Function.update x e true) = true ∧ f (Function.update x e false) = false
          then (1 : ℝ) else 0)) p := by
  convert hasDerivAt_sum_biasedWeight_mul p fun x => if f x = true then (1 : ℝ) else 0 using 1
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  by_cases h2 : f (Function.update x e false) = true
  · have h1 : f (Function.update x e true) = true := hf _ _ (fun y hy => by
      by_cases hye : y = e
      · simp [hye]
      · simpa [Function.update_apply, hye] using hy) h2
    simp [h1, h2]
  · by_cases h1 : f (Function.update x e true) = true <;> simp [h1, h2]

end Config

end

end TheoremOS.Probability
