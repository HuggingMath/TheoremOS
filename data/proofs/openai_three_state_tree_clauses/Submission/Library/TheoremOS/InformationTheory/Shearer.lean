import Submission.Library.TheoremOS.InformationTheory.Entropy

/-!
# Submodularity of joint entropy and Shearer's lemma

Shearer's lemma for an abstract monotone submodular set function `f` with `f ∅ = 0`, in a
fractional form (weights covering every point with total weight at least one) and in the
`k`-fold cover form; Han's inequality is the cover by the sets `U \ {i}`. The entropy layer:
the law `pushforward X p` of a random variable on a finite weighted space, monotonicity under
functions, invariance under injective maps, the inequality `H(X, Y) + H(Z) ≤ H(X) + H(Y)` when
`Z` is a function of `X` and of `Y` (nonnegativity of conditional mutual information),
`H(X, Y, Z) + H(Z) ≤ H(X, Z) + H(Y, Z)`, and the joint entropy `jointEntropy p X S` of a
subfamily `(X i)_{i ∈ S}` as a monotone submodular set function. Counting: for a finite family
`𝓕` of functions on a finite index type and a `k`-fold cover `F`,
`#𝓕 ^ k ≤ ∏ j, #(𝓕 restricted to F j)`, and the discrete Loomis–Whitney inequality
`#𝓕 ^ (n - 1) ≤ ∏ i, #(𝓕 restricted to the complement of i)`.

Sources: F. R. K. Chung, R. L. Graham, P. Frankl and J. B. Shearer, *Some intersection theorems
for ordered sets and graphs*, J. Combin. Theory Ser. A 43 (1986) 23–37 (Shearer's lemma);
T. S. Han, *Nonnegative entropy measures of multivariate symmetric correlations*, Inform. and
Control 36 (1978) 133–156; J. Radhakrishnan, *Entropy and counting*, in Computational
Mathematics, Modelling and Algorithms, 2003 (Shearer's lemma and the projection bound);
M. Madiman and P. Tetali, *Information inequalities for joint distributions, with
interpretations and applications*, IEEE Trans. Inform. Theory 56 (2010) 2699–2713 (fractional
covers of submodular functions); T. M. Cover and J. A. Thomas, *Elements of Information
Theory*, 2nd ed., Wiley, 2006, Sections 2.5–2.6 and 17.6. Textbook material; nothing here is
specific to a benchmark problem.

Bridges: `pushforward X p` is the law of `X : Ω → α` under weights `p` on `Ω`; a statement about
weights `r` on a product `∀ i, β i` is `jointEntropy r (fun i x => x i) univ = entropy r`
(`jointEntropy_univ_coord`); a family of random variables `X : ι → Ω → α` with a common value
type is the constant-family case `β := fun _ => α`.
-/

namespace TheoremOS.InformationTheory

open Finset Real
open scoped BigOperators

noncomputable section

/-! ### Shearer's lemma for submodular set functions -/

section Submodular

variable {ι : Type*} [DecidableEq ι] {f : Finset ι → ℝ}

/-- Diminishing returns: adding `a ∉ U` to `B ⊆ U` gains at least as much as adding it to `U`. -/
lemma submodular_insert_sub_le
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) {B U : Finset ι} {a : ι} (hBU : B ⊆ U)
    (ha : a ∉ U) : f (insert a U) - f U ≤ f (insert a B) - f B := by
  have h := hsub (insert a B) U
  rw [insert_union, union_eq_right.2 hBU, insert_inter_of_notMem ha, inter_eq_left.2 hBU] at h
  linarith

/-- **Shearer's lemma, fractional form**, for a monotone submodular `f` with `f ∅ = 0`: if every
point of `U` lies in sets `F j` of total weight at least one, then `f U ≤ ∑ j, w j f (U ∩ F j)`. -/
theorem fractional_shearer_of_submodular (hmono : ∀ S T, S ⊆ T → f S ≤ f T)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) (hempty : f ∅ = 0) {κ : Type*}
    (s : Finset κ) (F : κ → Finset ι) {w : κ → ℝ} (hw : ∀ j ∈ s, 0 ≤ w j) (U : Finset ι)
    (hcover : ∀ i ∈ U, 1 ≤ ∑ j ∈ s with i ∈ F j, w j) :
    f U ≤ ∑ j ∈ s, w j * f (U ∩ F j) := by
  induction U using Finset.induction_on with
  | empty =>
    simp only [empty_inter, hempty, mul_zero, sum_const_zero, le_refl]
  | @insert a U haU ih =>
    have ih := ih fun i hi => hcover i (mem_insert_of_mem hi)
    have ha := hcover a (mem_insert_self a U)
    set δ := f (insert a U) - f U with hδ
    have hδ0 : 0 ≤ δ := sub_nonneg.2 (hmono _ _ (subset_insert a U))
    have hterm : ∀ j ∈ s, (if a ∈ F j then w j else 0) * δ ≤
        w j * (f (insert a U ∩ F j) - f (U ∩ F j)) := by
      intro j hj
      by_cases haF : a ∈ F j
      · rw [ite_eq_left haF, insert_inter_of_mem haF]
        exact mul_le_mul_of_nonneg_left
          (submodular_insert_sub_le hsub inter_subset_left haU) (hw j hj)
      · rw [ite_eq_right haF, insert_inter_of_notMem haF, sub_self, mul_zero, zero_mul]
    have hsum : δ ≤ ∑ j ∈ s, w j * (f (insert a U ∩ F j) - f (U ∩ F j)) := by
      calc δ ≤ (∑ j ∈ s with a ∈ F j, w j) * δ := le_mul_of_one_le_left hδ0 ha
        _ = ∑ j ∈ s, (if a ∈ F j then w j else 0) * δ := by rw [sum_filter, sum_mul]
        _ ≤ _ := sum_le_sum hterm
    have hsplit : ∑ j ∈ s, w j * f (insert a U ∩ F j) =
        ∑ j ∈ s, w j * f (U ∩ F j) +
          ∑ j ∈ s, w j * (f (insert a U ∩ F j) - f (U ∩ F j)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ => by ring
    linarith

omit [DecidableEq ι] in
lemma nonneg_of_submodular (hmono : ∀ S T, S ⊆ T → f S ≤ f T) (hempty : f ∅ = 0)
    (S : Finset ι) : 0 ≤ f S := by
  simpa [hempty] using hmono ∅ S (empty_subset S)

/-- **Shearer's lemma** for a monotone submodular `f` with `f ∅ = 0`: if every point of `U`
lies in at least `k` of the sets `F j`, `j ∈ s`, then `k f U ≤ ∑ j ∈ s, f (U ∩ F j)`. -/
theorem shearer_of_submodular (hmono : ∀ S T, S ⊆ T → f S ≤ f T)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) (hempty : f ∅ = 0) {κ : Type*}
    (s : Finset κ) (F : κ → Finset ι) {k : ℕ} (U : Finset ι)
    (hcover : ∀ i ∈ U, k ≤ #{j ∈ s | i ∈ F j}) :
    k * f U ≤ ∑ j ∈ s, f (U ∩ F j) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, zero_mul]
    exact sum_nonneg fun j _ => nonneg_of_submodular hmono hempty _
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have h := fractional_shearer_of_submodular hmono hsub hempty s F (w := fun _ => (k : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.2 hk'.le) U (fun i hi => by
      simp only [sum_const, nsmul_eq_mul]
      rw [le_mul_inv_iff₀ hk', one_mul]
      exact_mod_cast hcover i hi)
  rw [← mul_sum] at h
  rw [← le_inv_mul_iff₀ hk']
  exact h

/-- **Han's inequality** for a monotone submodular `f` with `f ∅ = 0`:
`(|U| - 1) f U ≤ ∑ i ∈ U, f (U \ {i})`. -/
theorem han_of_submodular (hmono : ∀ S T, S ⊆ T → f S ≤ f T)
    (hsub : ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T) (hempty : f ∅ = 0) (U : Finset ι) :
    ((#U - 1 : ℕ) : ℝ) * f U ≤ ∑ i ∈ U, f (U.erase i) := by
  have h := shearer_of_submodular hmono hsub hempty U (fun i => U.erase i) (k := #U - 1) U
    (fun i hi => by
      rw [← card_erase_of_mem hi]
      exact card_le_card fun j hj => mem_filter.2
        ⟨mem_of_mem_erase hj, mem_erase.2 ⟨fun h => ne_of_mem_erase hj h.symm, hi⟩⟩)
  simpa only [inter_erase, inter_self] using h

end Submodular

/-! ### Entropy of random variables on a finite weighted space -/

section RandomVariable

variable {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Integrating against the law: `∑ a, (X_* p) a φ a = ∑ ω, p ω φ (X ω)`. -/
lemma sum_pushforward_mul (X : Ω → α) (p : Ω → ℝ) (φ : α → ℝ) :
    ∑ a, pushforward X p a * φ a = ∑ ω, p ω * φ (X ω) := by
  calc ∑ a, pushforward X p a * φ a = ∑ a, ∑ ω with X ω = a, p ω * φ (X ω) := by
        refine sum_congr rfl fun a _ => ?_
        rw [pushforward, sum_mul]
        exact sum_congr rfl fun ω hω => by rw [(mem_filter.1 hω).2]
    _ = ∑ ω, p ω * φ (X ω) := sum_fiberwise univ X fun ω => p ω * φ (X ω)

omit [Fintype α] [DecidableEq α] in
lemma pushforward_id [DecidableEq Ω] (p : Ω → ℝ) : pushforward (fun ω => ω) p = p := by
  funext ω
  simp [pushforward, filter_eq']

omit [Fintype β] in
/-- The law of `g ∘ X` is the pushforward of the law of `X`. -/
lemma pushforward_comp (X : Ω → α) (g : α → β) (p : Ω → ℝ) :
    pushforward g (pushforward X p) = pushforward (fun ω => g (X ω)) p := by
  funext b
  have h := sum_pushforward_mul X p fun a => if g a = b then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, ← sum_filter] at h
  exact h

omit [Fintype α] in
lemma pushforward_nonneg {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → α) (a : α) :
    0 ≤ pushforward X p a :=
  sum_nonneg fun ω _ => hp ω

/-- **Data processing**: `H(g(X)) ≤ H(X)`. -/
theorem entropy_pushforward_comp_le {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : Ω → α) (g : α → β) :
    entropy (pushforward (fun ω => g (X ω)) p) ≤ entropy (pushforward X p) := by
  rw [← pushforward_comp]
  exact entropy_pushforward_le (pushforward_nonneg hp X) g

/-- Random variables that are functions of each other have the same entropy. -/
theorem entropy_pushforward_eq_of_comp {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {X : Ω → α}
    {Y : Ω → β} (f : α → β) (g : β → α) (hY : ∀ ω, Y ω = f (X ω)) (hX : ∀ ω, X ω = g (Y ω)) :
    entropy (pushforward Y p) = entropy (pushforward X p) := by
  have hY' : Y = fun ω => f (X ω) := funext hY
  have hX' : X = fun ω => g (Y ω) := funext hX
  refine le_antisymm ?_ ?_
  · rw [hY']; exact entropy_pushforward_comp_le hp X f
  · rw [hX']; exact entropy_pushforward_comp_le hp Y g

omit [Fintype α] in
lemma pushforward_const {p : Ω → ℝ} (hp : IsDistribution p) (a : α) :
    pushforward (fun _ => a) p = fun b => if b = a then 1 else 0 := by
  funext b
  by_cases h : b = a
  · subst h
    simp [pushforward, hp.sum_eq_one]
  · simp [pushforward, Ne.symm h, h]

/-- A constant has entropy zero. -/
lemma entropy_pushforward_const {p : Ω → ℝ} (hp : IsDistribution p) (a : α) :
    entropy (pushforward (fun _ => a) p) = 0 := by
  rw [pushforward_const hp, entropy]
  exact sum_eq_zero fun b _ => by split_ifs <;> simp

/-- The law of an injective image has the same entropy. -/
theorem entropy_pushforward_of_injective {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) {g : Ω → α}
    (hg : Function.Injective g) : entropy (pushforward g p) = entropy p := by
  classical
  refine le_antisymm (entropy_pushforward_le hp g) ?_
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · simp [entropy, pushforward]
  have hinv : ∀ ω, Function.invFun g (g ω) = ω := Function.leftInverse_invFun hg
  calc entropy p = entropy (pushforward (fun ω => Function.invFun g (g ω)) p) := by
        simp only [hinv, pushforward_id]
    _ ≤ entropy (pushforward g p) :=
        entropy_pushforward_comp_le hp g (Function.invFun g)

/-- **Submodularity of entropy**: if `Z = g(X) = h(Y)` is a common function of `X` and `Y`, then
`H(X, Y) + H(Z) ≤ H(X) + H(Y)`; this is `I(X; Y | Z) ≥ 0`. -/
theorem entropy_pair_add_le {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → α) (Y : Ω → β)
    (g : α → γ) (h : β → γ) (hgh : ∀ ω, g (X ω) = h (Y ω)) :
    entropy (pushforward (fun ω => (X ω, Y ω)) p) + entropy (pushforward (fun ω => g (X ω)) p) ≤
      entropy (pushforward X p) + entropy (pushforward Y p) := by
  obtain ⟨r, hr⟩ : ∃ r, r = pushforward (fun ω => (X ω, Y ω)) p := ⟨_, rfl⟩
  obtain ⟨r₁, hr₁⟩ : ∃ r₁, r₁ = pushforward X p := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = pushforward Y p := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = pushforward (fun ω => g (X ω)) p := ⟨_, rfl⟩
  rw [← hr, ← hr₁, ← hr₂, ← hL]
  have hrd : IsDistribution r := by rw [hr]; exact hp.pushforward _
  have hr0 : ∀ x, 0 ≤ r x := hrd.nonneg
  have hr₁0 : ∀ a, 0 ≤ r₁ a := fun a => by rw [hr₁]; exact pushforward_nonneg hp.nonneg X a
  have hr₂0 : ∀ b, 0 ≤ r₂ b := fun b => by rw [hr₂]; exact pushforward_nonneg hp.nonneg Y b
  have hL0 : ∀ c, 0 ≤ L c := fun c => by rw [hL]; exact pushforward_nonneg hp.nonneg _ c
  have hfst : pushforward Prod.fst r = r₁ := by rw [hr, hr₁, pushforward_comp]
  have hsnd : pushforward Prod.snd r = r₂ := by rw [hr, hr₂, pushforward_comp]
  have hLX : pushforward g r₁ = L := by rw [hr₁, hL, pushforward_comp]
  have hLY : pushforward h r₂ = L := by
    rw [hr₂, hL, pushforward_comp]
    exact congrArg (fun F => pushforward F p) (funext fun ω => (hgh ω).symm)
  have hsupp : ∀ x : α × β, r x ≠ 0 → g x.1 = h x.2 := by
    intro x hx
    rw [hr] at hx
    obtain ⟨ω, hω, -⟩ := exists_ne_zero_of_sum_ne_zero hx
    have hxω : (X ω, Y ω) = x := (mem_filter.1 hω).2
    subst hxω
    exact hgh ω
  have hle₁ : ∀ x : α × β, r x ≤ r₁ x.1 := by
    intro x
    rw [← hfst]
    exact single_le_sum (fun y _ => hr0 y) (mem_filter.2 ⟨mem_univ x, rfl⟩)
  have hle₂ : ∀ x : α × β, r x ≤ r₂ x.2 := by
    intro x
    rw [← hsnd]
    exact single_le_sum (fun y _ => hr0 y) (mem_filter.2 ⟨mem_univ x, rfl⟩)
  have hLge : ∀ a, r₁ a ≤ L (g a) := by
    intro a
    rw [← hLX]
    exact single_le_sum (fun y _ => hr₁0 y) (mem_filter.2 ⟨mem_univ a, rfl⟩)
  obtain ⟨q, hq⟩ : ∃ q : α × β → ℝ, ∀ a b,
      q (a, b) = if g a = h b then r₁ a * r₂ b / L (g a) else 0 :=
    ⟨fun x => if g x.1 = h x.2 then r₁ x.1 * r₂ x.2 / L (g x.1) else 0, fun _ _ => rfl⟩
  have hpos : ∀ a b, r (a, b) ≠ 0 → 0 < r₁ a ∧ 0 < r₂ b ∧ 0 < L (g a) := by
    intro a b hx
    have h1 : 0 < r₁ a := lt_of_lt_of_le ((hr0 _).lt_of_ne (Ne.symm hx)) (hle₁ (a, b))
    have h2 : 0 < r₂ b := lt_of_lt_of_le ((hr0 _).lt_of_ne (Ne.symm hx)) (hle₂ (a, b))
    exact ⟨h1, h2, lt_of_lt_of_le h1 (hLge a)⟩
  have hq0 : ∀ x, 0 ≤ q x := by
    rintro ⟨a, b⟩
    rw [hq]
    split_ifs
    · exact div_nonneg (mul_nonneg (hr₁0 a) (hr₂0 b)) (hL0 _)
    · exact le_rfl
  have hqr : ∀ x, q x = 0 → r x = 0 := by
    rintro ⟨a, b⟩ hqx
    by_contra hx
    have hab : g a = h b := hsupp (a, b) hx
    obtain ⟨h1, h2, h3⟩ := hpos a b hx
    rw [hq, ite_eq_left hab] at hqx
    exact (div_pos (mul_pos h1 h2) h3).ne' hqx
  have hqsum : ∑ x, q x ≤ ∑ x, r x := by
    rw [hrd.sum_eq_one, Fintype.sum_prod_type]
    calc ∑ a, ∑ b, q (a, b) = ∑ a, r₁ a / L (g a) * ∑ b with h b = g a, r₂ b := by
          refine sum_congr rfl fun a _ => ?_
          rw [mul_sum, sum_filter]
          refine sum_congr rfl fun b _ => ?_
          rw [hq]
          by_cases hab : g a = h b
          · rw [ite_eq_left hab, ite_eq_left hab.symm]
            ring
          · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab)]
      _ = ∑ a, r₁ a / L (g a) * L (g a) := by
          refine sum_congr rfl fun a _ => ?_
          rw [← hLY]
          rfl
      _ ≤ ∑ a, r₁ a := by
          refine sum_le_sum fun a _ => ?_
          rcases (hL0 (g a)).eq_or_lt with h0 | h0
          · rw [← h0, mul_zero]
            exact hr₁0 a
          · exact (div_mul_cancel₀ (r₁ a) h0.ne').le
      _ = 1 := by rw [hr₁]; exact (hp.pushforward X).sum_eq_one
  have hlog : ∑ x, r x * log (q x) = ∑ x, r x * log (r₁ x.1) + ∑ x, r x * log (r₂ x.2) -
      ∑ x, r x * log (L (g x.1)) := by
    rw [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl ?_
    rintro ⟨a, b⟩ _
    dsimp only
    by_cases hx : r (a, b) = 0
    · simp [hx]
    obtain ⟨h1, h2, h3⟩ := hpos a b hx
    rw [hq, ite_eq_left (hsupp (a, b) hx), log_div (mul_pos h1 h2).ne' h3.ne',
      log_mul h1.ne' h2.ne']
    ring
  have hs1 : ∑ x, r x * log (r₁ x.1) = -entropy r₁ := by
    rw [entropy_eq_neg_sum, neg_neg, ← hfst, sum_pushforward_mul]
  have hs2 : ∑ x, r x * log (r₂ x.2) = -entropy r₂ := by
    rw [entropy_eq_neg_sum, neg_neg, ← hsnd, sum_pushforward_mul]
  have hLr : pushforward (fun x : α × β => g x.1) r = L := by
    rw [← hLX, ← hfst, pushforward_comp]
  have hsL : ∑ x, r x * log (L (g x.1)) = -entropy L := by
    rw [entropy_eq_neg_sum, neg_neg, ← hLr, sum_pushforward_mul]
  have hgibbs := sum_mul_log_le_sum_mul_log hr0 hq0 hqr hqsum
  rw [hlog, hs1, hs2, hsL] at hgibbs
  rw [entropy_eq_neg_sum r]
  linarith

/-- **Subadditivity**: `H(X, Y) ≤ H(X) + H(Y)`. -/
theorem entropy_pair_le {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → α) (Y : Ω → β) :
    entropy (pushforward (fun ω => (X ω, Y ω)) p) ≤
      entropy (pushforward X p) + entropy (pushforward Y p) := by
  have h := entropy_pair_add_le hp X Y (fun _ => ()) (fun _ => ()) fun _ => rfl
  have h0 : entropy (pushforward (fun _ : Ω => ()) p) = 0 := entropy_pushforward_const hp ()
  linarith

/-- **Submodularity**, three-variable form: `H(X, Y, Z) + H(Z) ≤ H(X, Z) + H(Y, Z)`. -/
theorem entropy_triple_add_le {p : Ω → ℝ} (hp : IsDistribution p) (X : Ω → α) (Y : Ω → β)
    (Z : Ω → γ) :
    entropy (pushforward (fun ω => (X ω, Y ω, Z ω)) p) + entropy (pushforward Z p) ≤
      entropy (pushforward (fun ω => (X ω, Z ω)) p) +
        entropy (pushforward (fun ω => (Y ω, Z ω)) p) := by
  have h := entropy_pair_add_le hp (fun ω => (X ω, Z ω)) (fun ω => (Y ω, Z ω))
    Prod.snd Prod.snd fun _ => rfl
  have e : entropy (pushforward (fun ω => ((X ω, Z ω), (Y ω, Z ω))) p) =
      entropy (pushforward (fun ω => (X ω, Y ω, Z ω)) p) :=
    entropy_pushforward_eq_of_comp hp.nonneg (fun t => ((t.1, t.2.2), (t.2.1, t.2.2)))
      (fun s => (s.1.1, s.2.1, s.1.2)) (fun _ => rfl) (fun _ => rfl)
  have h' : entropy (pushforward (fun ω => ((X ω, Z ω), (Y ω, Z ω))) p) +
      entropy (pushforward Z p) ≤ entropy (pushforward (fun ω => (X ω, Z ω)) p) +
        entropy (pushforward (fun ω => (Y ω, Z ω)) p) := h
  linarith

end RandomVariable

/-! ### Joint entropy of subfamilies -/

section Family

variable {ι Ω : Type*} [DecidableEq ι] {β : ι → Type*}

/-- The subfamily `(X i ω)_{i ∈ S}`, with `none` off `S`. -/
def restrictOpt (X : ∀ i, Ω → β i) (S : Finset ι) (ω : Ω) : ∀ i, Option (β i) :=
  fun i => if i ∈ S then some (X i ω) else none

/-- Forget the coordinates outside `S`. -/
def maskOpt (S : Finset ι) (y : ∀ i, Option (β i)) : ∀ i, Option (β i) :=
  fun i => if i ∈ S then y i else none

lemma maskOpt_restrictOpt (X : ∀ i, Ω → β i) (S T : Finset ι) (ω : Ω) :
    maskOpt S (restrictOpt X T ω) = restrictOpt X (T ∩ S) ω := by
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [maskOpt, restrictOpt, hS, hT]

lemma restrictOpt_empty (X : ∀ i, Ω → β i) : restrictOpt X ∅ = fun _ _ => none := by
  funext ω i
  simp [restrictOpt]

variable [Fintype ι] [Fintype Ω] [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]

/-- The joint entropy `H((X i)_{i ∈ S})` under weights `p`. -/
def jointEntropy (p : Ω → ℝ) (X : ∀ i, Ω → β i) (S : Finset ι) : ℝ :=
  entropy (pushforward (restrictOpt X S) p)

lemma jointEntropy_empty {p : Ω → ℝ} (hp : IsDistribution p) (X : ∀ i, Ω → β i) :
    jointEntropy p X ∅ = 0 := by
  rw [jointEntropy, restrictOpt_empty]
  exact entropy_pushforward_const hp _

lemma jointEntropy_mono {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : ∀ i, Ω → β i) {S T : Finset ι}
    (hST : S ⊆ T) : jointEntropy p X S ≤ jointEntropy p X T := by
  have h : restrictOpt X S = fun ω => maskOpt S (restrictOpt X T ω) := by
    funext ω
    rw [maskOpt_restrictOpt, inter_eq_right.2 hST]
  unfold jointEntropy
  rw [h]
  exact entropy_pushforward_comp_le hp (restrictOpt X T) (maskOpt S)

/-- **Submodularity of joint entropy**: `H(X_{S ∪ T}) + H(X_{S ∩ T}) ≤ H(X_S) + H(X_T)`. -/
theorem jointEntropy_union_add_inter_le {p : Ω → ℝ} (hp : IsDistribution p)
    (X : ∀ i, Ω → β i) (S T : Finset ι) :
    jointEntropy p X (S ∪ T) + jointEntropy p X (S ∩ T) ≤
      jointEntropy p X S + jointEntropy p X T := by
  have h := entropy_pair_add_le hp (restrictOpt X S) (restrictOpt X T) (maskOpt T) (maskOpt S)
    fun ω => by rw [maskOpt_restrictOpt, maskOpt_restrictOpt, inter_comm]
  have hT : (fun ω => maskOpt T (restrictOpt X S ω)) = restrictOpt X (S ∩ T) := by
    funext ω
    rw [maskOpt_restrictOpt]
  have e := entropy_pushforward_eq_of_comp hp.nonneg (X := restrictOpt X (S ∪ T))
    (Y := fun ω => (restrictOpt X S ω, restrictOpt X T ω))
    (fun y => (maskOpt S y, maskOpt T y)) (fun z i => if i ∈ S then z.1 i else z.2 i)
    (fun ω => by
      rw [maskOpt_restrictOpt, maskOpt_restrictOpt, union_inter_cancel_left,
        union_inter_cancel_right])
    (fun ω => by
      funext i
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [restrictOpt, hS, hT])
  rw [hT, e] at h
  exact h

/-- **Shearer's lemma** for entropy: if every coordinate of `U` lies in at least `k` of the sets
`F j`, `j ∈ s`, then `k H(X_U) ≤ ∑ j ∈ s, H(X_{U ∩ F j})`. -/
theorem jointEntropy_shearer {p : Ω → ℝ} (hp : IsDistribution p) (X : ∀ i, Ω → β i)
    {κ : Type*} (s : Finset κ) (F : κ → Finset ι) {k : ℕ} (U : Finset ι)
    (hcover : ∀ i ∈ U, k ≤ #{j ∈ s | i ∈ F j}) :
    k * jointEntropy p X U ≤ ∑ j ∈ s, jointEntropy p X (U ∩ F j) :=
  shearer_of_submodular (f := jointEntropy p X) (fun _ _ h => jointEntropy_mono hp.nonneg X h)
    (jointEntropy_union_add_inter_le hp X) (jointEntropy_empty hp X) s F U hcover

/-- **Shearer's lemma**, fractional form: if every coordinate of `U` lies in sets `F j` of total
weight at least one, then `H(X_U) ≤ ∑ j ∈ s, w j H(X_{U ∩ F j})`. -/
theorem jointEntropy_fractional_shearer {p : Ω → ℝ} (hp : IsDistribution p)
    (X : ∀ i, Ω → β i) {κ : Type*} (s : Finset κ) (F : κ → Finset ι) {w : κ → ℝ}
    (hw : ∀ j ∈ s, 0 ≤ w j) (U : Finset ι) (hcover : ∀ i ∈ U, 1 ≤ ∑ j ∈ s with i ∈ F j, w j) :
    jointEntropy p X U ≤ ∑ j ∈ s, w j * jointEntropy p X (U ∩ F j) :=
  fractional_shearer_of_submodular (f := jointEntropy p X)
    (fun _ _ h => jointEntropy_mono hp.nonneg X h) (jointEntropy_union_add_inter_le hp X)
    (jointEntropy_empty hp X) s F hw U hcover

/-- **Han's inequality**: `(|U| - 1) H(X_U) ≤ ∑ i ∈ U, H(X_{U \ {i}})`. -/
theorem jointEntropy_han {p : Ω → ℝ} (hp : IsDistribution p) (X : ∀ i, Ω → β i)
    (U : Finset ι) :
    ((#U - 1 : ℕ) : ℝ) * jointEntropy p X U ≤ ∑ i ∈ U, jointEntropy p X (U.erase i) :=
  han_of_submodular (f := jointEntropy p X) (fun _ _ h => jointEntropy_mono hp.nonneg X h)
    (jointEntropy_union_add_inter_le hp X) (jointEntropy_empty hp X) U

/-- The joint entropy of the whole family is the entropy of the law of the tuple. -/
lemma jointEntropy_univ {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : ∀ i, Ω → β i) :
    jointEntropy p X univ = entropy (pushforward (fun ω i => X i ω) p) := by
  have hinj : Function.Injective fun (y : ∀ i, β i) (i : ι) => some (y i) :=
    fun y z h => funext fun i => Option.some.inj (congrFun h i)
  have h : pushforward (fun (y : ∀ i, β i) (i : ι) => some (y i))
      (pushforward (fun ω i => X i ω) p) = pushforward (restrictOpt X univ) p := by
    rw [pushforward_comp]
    congr 1
    funext ω i
    simp [restrictOpt]
  rw [jointEntropy, ← h]
  exact entropy_pushforward_of_injective (pushforward_nonneg hp _) hinj

/-- For weights `r` on a product, the coordinates have joint entropy `entropy r`. -/
lemma jointEntropy_univ_coord {r : (∀ i, β i) → ℝ} (hr : ∀ x, 0 ≤ r x) :
    jointEntropy r (fun i x => x i) univ = entropy r := by
  rw [jointEntropy_univ hr, pushforward_id]

/-- The joint entropy of one coordinate is its entropy. -/
lemma jointEntropy_singleton {p : Ω → ℝ} (hp : ∀ ω, 0 ≤ p ω) (X : ∀ i, Ω → β i) (i : ι) :
    jointEntropy p X {i} = entropy (pushforward (X i) p) := by
  have hinj : Function.Injective fun b : β i => Function.update (fun _ => none) i (some b) :=
    fun b c h => by simpa using congrFun h i
  have h : pushforward (fun b : β i => Function.update (fun _ => none) i (some b))
      (pushforward (X i) p) = pushforward (restrictOpt X {i}) p := by
    rw [pushforward_comp]
    congr 1
    funext ω j
    by_cases hj : j = i
    · subst hj
      simp [restrictOpt]
    · simp [restrictOpt, hj]
  rw [jointEntropy, ← h]
  exact entropy_pushforward_of_injective (pushforward_nonneg hp _) hinj

/-- **Subadditivity**: `H((X i)_i) ≤ ∑ i, H(X i)`. -/
theorem jointEntropy_univ_le_sum {p : Ω → ℝ} (hp : IsDistribution p) (X : ∀ i, Ω → β i) :
    jointEntropy p X univ ≤ ∑ i, entropy (pushforward (X i) p) := by
  have h := jointEntropy_shearer hp X univ (fun i => {i}) (k := 1) univ fun i _ =>
    card_pos.2 ⟨i, mem_filter.2 ⟨mem_univ i, mem_singleton_self i⟩⟩
  simp only [Nat.cast_one, one_mul, univ_inter] at h
  simpa only [jointEntropy_singleton hp.nonneg] using h

end Family

/-! ### Counting: projections of a finite family of functions -/

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

lemma isDistribution_uniformOn {A : Finset α} (hA : A.Nonempty) :
    IsDistribution (fun a => if a ∈ A then (#A : ℝ)⁻¹ else 0) where
  nonneg a := by positivity
  sum_eq_one := by
    have hc : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 hA).ne'
    rw [Fintype.sum_ite_mem, sum_const, nsmul_eq_mul, mul_inv_cancel₀ hc]

/-- The uniform distribution on `A` has entropy `log |A|`. -/
lemma entropy_uniformOn (A : Finset α) :
    entropy (fun a => if a ∈ A then (#A : ℝ)⁻¹ else 0) = log #A := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [entropy]
  have hc : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 hA).ne'
  simp only [entropy, apply_ite negMulLog, negMulLog_zero, Fintype.sum_ite_mem, sum_const,
    nsmul_eq_mul]
  rw [negMulLog, log_inv, neg_mul_neg, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

/-- `H q ≤ log |A|` for a distribution `q` vanishing off `A`. -/
theorem entropy_le_log_card_of_support {q : α → ℝ} (hq : IsDistribution q) {A : Finset α}
    (hA : ∀ a ∉ A, q a = 0) : entropy q ≤ log #A := by
  have hsum : ∑ a ∈ A, q a = 1 := by
    rw [← hq.sum_eq_one]
    exact sum_subset (subset_univ A) fun a _ ha => hA a ha
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h
    · simp at hsum
    · exact h
  have hc : (#A : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 hne).ne'
  have h := entropy_le_crossEntropy hq (isDistribution_uniformOn hne) fun a ha => by
    by_cases haA : a ∈ A
    · simp [haA, hc] at ha
    · exact hA a haA
  have hcross : ∑ a, q a * log (if a ∈ A then (#A : ℝ)⁻¹ else 0) = -log #A := by
    rw [← sum_subset (subset_univ A) fun a _ ha => by simp [hA a ha]]
    rw [sum_congr rfl fun a ha => by rw [ite_eq_left ha, log_inv], ← sum_mul, hsum]
    ring
  rw [hcross, neg_neg] at h
  exact h

omit [Fintype α] in
lemma pushforward_eq_zero_of_notMem_image {Ω : Type*} [Fintype Ω] {q : Ω → ℝ} {A : Finset Ω}
    (hA : ∀ ω ∉ A, q ω = 0) (f : Ω → α) {b : α} (hb : b ∉ A.image f) :
    pushforward f q b = 0 :=
  sum_eq_zero fun ω hω => hA ω fun hωA =>
    hb (by rw [← (mem_filter.1 hω).2]; exact mem_image_of_mem f hωA)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

omit [∀ i, Fintype (β i)] in
lemma card_image_restrictOpt (𝓕 : Finset (∀ i, β i)) (S : Finset ι) :
    #(𝓕.image (restrictOpt (fun i x => x i) S)) = #(𝓕.image S.restrict) := by
  have hinj : Function.Injective fun (y : ∀ i : S, β i) (i : ι) =>
      if hi : i ∈ S then some (y ⟨i, hi⟩) else none := by
    intro y z h
    funext i
    simpa [i.2] using congrFun h i
  have h : 𝓕.image (restrictOpt (fun i x => x i) S) = (𝓕.image S.restrict).image
      fun (y : ∀ i : S, β i) (i : ι) => if hi : i ∈ S then some (y ⟨i, hi⟩) else none := by
    rw [image_image]
    congr 1
  rw [h, card_image_of_injective _ hinj]

/-- **Shearer's lemma, counting form**: if every coordinate lies in at least `k` of the sets
`F j`, `j ∈ s`, then `k log |𝓕| ≤ ∑ j ∈ s, log |𝓕 restricted to F j|`. -/
theorem log_card_shearer (𝓕 : Finset (∀ i, β i)) {κ : Type*} (s : Finset κ) (F : κ → Finset ι)
    {k : ℕ} (hcover : ∀ i, k ≤ #{j ∈ s | i ∈ F j}) :
    k * log #𝓕 ≤ ∑ j ∈ s, log #(𝓕.image (F j).restrict) := by
  rcases 𝓕.eq_empty_or_nonempty with rfl | hne
  · simp
  have hu := isDistribution_uniformOn hne
  have h := jointEntropy_shearer hu (fun i x => x i) s F univ fun i _ => hcover i
  rw [jointEntropy_univ_coord hu.nonneg, entropy_uniformOn] at h
  refine h.trans (sum_le_sum fun j _ => ?_)
  rw [univ_inter, ← card_image_restrictOpt, jointEntropy]
  refine entropy_le_log_card_of_support (hu.pushforward _) fun y hy =>
    pushforward_eq_zero_of_notMem_image (fun x hx => ?_) _ hy
  simp [hx]

/-- **Shearer's lemma, product form**: if every coordinate lies in at least `k ≠ 0` of the sets
`F j`, `j ∈ s`, then `|𝓕| ^ k ≤ ∏ j ∈ s, |𝓕 restricted to F j|`. -/
theorem card_pow_le_prod_card_shearer (𝓕 : Finset (∀ i, β i)) {κ : Type*} (s : Finset κ)
    (F : κ → Finset ι) {k : ℕ} (hk : k ≠ 0) (hcover : ∀ i, k ≤ #{j ∈ s | i ∈ F j}) :
    #𝓕 ^ k ≤ ∏ j ∈ s, #(𝓕.image (F j).restrict) := by
  rcases 𝓕.eq_empty_or_nonempty with rfl | hne
  · simp [zero_pow hk]
  have hpos : ∀ j ∈ s, (0 : ℝ) < #(𝓕.image (F j).restrict) := fun j _ =>
    Nat.cast_pos.2 (card_pos.2 (hne.image _))
  have h := log_card_shearer 𝓕 s F hcover
  rw [← log_pow, ← log_prod fun j hj => (hpos j hj).ne'] at h
  have h' : ((#𝓕 : ℝ) ^ k) ≤ ∏ j ∈ s, (#(𝓕.image (F j).restrict) : ℝ) :=
    (log_le_log_iff (pow_pos (Nat.cast_pos.2 (card_pos.2 hne)) k) (prod_pos hpos)).1 h
  exact_mod_cast h'

omit [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)] in
lemma card_erase_cover (i : ι) : Fintype.card ι - 1 ≤ #{j | i ∈ (univ : Finset ι).erase j} := by
  rw [← Finset.card_univ, ← card_erase_of_mem (mem_univ i)]
  exact card_le_card fun j hj => mem_filter.2
    ⟨mem_univ j, mem_erase.2 ⟨fun h => ne_of_mem_erase hj h.symm, mem_univ i⟩⟩

/-- The **discrete Loomis–Whitney inequality**, logarithmic form:
`(n - 1) log |𝓕| ≤ ∑ i, log |𝓕 restricted to ι \ {i}|` for `n = |ι|`. -/
theorem log_card_loomis_whitney (𝓕 : Finset (∀ i, β i)) :
    ((Fintype.card ι - 1 : ℕ) : ℝ) * log #𝓕 ≤
      ∑ i, log #(𝓕.image ((univ : Finset ι).erase i).restrict) :=
  log_card_shearer 𝓕 univ (fun i => univ.erase i) card_erase_cover

/-- The **discrete Loomis–Whitney inequality**: `|𝓕| ^ (n - 1) ≤ ∏ i, |𝓕 restricted to
ι \ {i}|` for `n = |ι| ≥ 2`. -/
theorem card_pow_le_prod_card_loomis_whitney (𝓕 : Finset (∀ i, β i))
    (hι : 2 ≤ Fintype.card ι) :
    #𝓕 ^ (Fintype.card ι - 1) ≤ ∏ i, #(𝓕.image ((univ : Finset ι).erase i).restrict) :=
  card_pow_le_prod_card_shearer 𝓕 univ (fun i => univ.erase i) (by omega) card_erase_cover

end Counting

end

end TheoremOS.InformationTheory
