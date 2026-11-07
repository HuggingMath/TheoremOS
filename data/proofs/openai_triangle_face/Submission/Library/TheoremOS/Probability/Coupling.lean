import Submission.Library.TheoremOS.Probability.SpectralGap

/-!
# Couplings and path coupling

Couplings of finite distributions and their use for Markov chains. Contents: `IsCoupling r p q`
(nonnegative weights on `Ω × Ω'` with marginals `p` and `q`), the product, diagonal, swapped and
point couplings; the coupling inequality `tvDist p q ≤ ∑_{x ≠ y} r(x, y)`; the **maximal
coupling** that attains it (`exists_isCoupling_tvDist_eq`); Markovian couplings `Q` of a kernel
`P` with itself (`IsMarkovianCoupling`), the iterated coupling `r ᵥ* Q ^ t` of `μ P^t` and
`ν P^t`, and the **coupling bound for chains** `tvDist (P^t x) (P^t y) ≤ P_{(x,y)}(X_t ≠ Y_t)`;
the transport cost `TransportLE ρ p q c` (a coupling with `∑ r ρ ≤ c`), its gluing triangle
inequality and its contraction under a kernel; and **path coupling** (Bubley–Dyer): if adjacent
pairs contract, `TransportLE ρ (K a) (K b) (κ ρ(a, b))`, and `ρ` is a path metric, then
`tvDist (K^t x) (K^t y) ≤ κ^t ρ(x, y)` and `tvDist (K^t x) π ≤ κ^t D` for a stationary `π`
with `∑ π y ρ(x, y) ≤ D`.

Sources: D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS, 2017,
Sections 4.2, 5.1–5.2 and 14.2 (Proposition 4.7, Theorem 5.4, Theorem 14.6); R. Bubley and
M. Dyer, Path coupling: a technique for proving rapid mixing in Markov chains, FOCS 1997;
T. Lindvall, *Lectures on the Coupling Method*, Wiley, 1992. Textbook material; nothing here is
specific to a benchmark problem.

Bridges: a kernel given as a function `K : Ω → Ω → ℝ` is a `Matrix Ω Ω ℝ`, and its `t`-th power
can be matched with `eq_pow_of_recursion`. For path coupling with the graph distance of a
neighbour relation, take `ρ x y` to be the distance, `E` the neighbour relation and `path x y`
a geodesic; `pathEdges` lists its consecutive pairs. `ρ x y ≥ 1` off the diagonal is what turns
transport cost into a total variation bound (`tvDist_le_of_transportLE`).
-/

namespace TheoremOS.Probability

open Finset Matrix
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

section Couplings

/-- `r` is a coupling of `p` and `q`. -/
structure IsCoupling (r : Ω × Ω' → ℝ) (p : Ω → ℝ) (q : Ω' → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ r x
  left : ∀ a, ∑ b, r (a, b) = p a
  right : ∀ b, ∑ a, r (a, b) = q b

variable {r : Ω × Ω' → ℝ} {p : Ω → ℝ} {q : Ω' → ℝ}

lemma IsCoupling.marginalLeft_eq (h : IsCoupling r p q) : marginalLeft r = p :=
  funext h.left

lemma IsCoupling.marginalRight_eq (h : IsCoupling r p q) : marginalRight r = q :=
  funext h.right

lemma IsCoupling.le_left (h : IsCoupling r p q) (a : Ω) (b : Ω') : r (a, b) ≤ p a := by
  rw [← h.left a]
  exact Finset.single_le_sum (f := fun b => r (a, b)) (fun b _ => h.nonneg _) (Finset.mem_univ b)

lemma IsCoupling.le_right (h : IsCoupling r p q) (a : Ω) (b : Ω') : r (a, b) ≤ q b := by
  rw [← h.right b]
  exact Finset.single_le_sum (f := fun a => r (a, b)) (fun a _ => h.nonneg _) (Finset.mem_univ a)

lemma IsCoupling.swap (h : IsCoupling r p q) : IsCoupling (fun x => r x.swap) q p :=
  ⟨fun _ => h.nonneg _, h.right, h.left⟩

lemma isCoupling_prod (hp : IsDistribution p) (hq : IsDistribution q) :
    IsCoupling (fun x => p x.1 * q x.2) p q :=
  ⟨fun x => mul_nonneg (hp.nonneg _) (hq.nonneg _),
    fun a => by simp [← Finset.mul_sum, hq.sum_eq_one],
    fun b => by simp [← Finset.sum_mul, hp.sum_eq_one]⟩

lemma isCoupling_diag [DecidableEq Ω] (hp : ∀ a, 0 ≤ p a) :
    IsCoupling (fun x : Ω × Ω => if x.1 = x.2 then p x.1 else 0) p p :=
  ⟨fun _ => by split_ifs <;> simp [hp], fun a => by simp, fun b => by simp⟩

lemma isCoupling_single [DecidableEq Ω] [DecidableEq Ω'] (a : Ω) (b : Ω') :
    IsCoupling (Pi.single (a, b) 1) (Pi.single a 1) (Pi.single b 1) := by
  have e : (Pi.single (a, b) 1 : Ω × Ω' → ℝ) =
      fun x => (Pi.single a 1 : Ω → ℝ) x.1 * (Pi.single b 1 : Ω' → ℝ) x.2 := funext fun x => by
    obtain ⟨x, y⟩ := x
    by_cases hx : x = a <;> by_cases hy : y = b <;> simp [hx, hy]
  rw [e]
  exact isCoupling_prod (isDistribution_single a) (isDistribution_single b)

/-- The **coupling inequality**: `tvDist p q ≤ P(X ≠ Y)`. -/
theorem IsCoupling.tvDist_le [DecidableEq Ω] {r : Ω × Ω → ℝ} {p q : Ω → ℝ}
    (h : IsCoupling r p q) : tvDist p q ≤ ∑ x with x.1 ≠ x.2, r x := by
  rw [← h.marginalLeft_eq, ← h.marginalRight_eq]
  exact tvDist_marginal_le h.nonneg

/-- The **maximal coupling**: some coupling attains `tvDist p q = P(X ≠ Y)`. -/
theorem exists_isCoupling_tvDist_eq [DecidableEq Ω] {p q : Ω → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) :
    ∃ r : Ω × Ω → ℝ, IsCoupling r p q ∧ ∑ x with x.1 ≠ x.2, r x = tvDist p q := by
  obtain ⟨t, ht⟩ : ∃ t, t = tvDist p q := ⟨_, rfl⟩
  rw [← ht]
  have hmin := tvDist_eq_one_sub_sum_min hp hq
  have hsp : ∑ a, (p a - min (p a) (q a)) = t := by
    rw [Finset.sum_sub_distrib, hp.sum_eq_one, ht]; linarith
  have hsq : ∑ a, (q a - min (p a) (q a)) = t := by
    rw [Finset.sum_sub_distrib, hq.sum_eq_one, ht]; linarith
  have hzero : ∀ a, (p a - min (p a) (q a)) * (q a - min (p a) (q a)) = 0 := fun a => by
    rcases le_total (p a) (q a) with h | h
    · rw [min_eq_left h, sub_self, zero_mul]
    · rw [min_eq_right h, sub_self, mul_zero]
  have hp0 : ∀ a, 0 ≤ p a - min (p a) (q a) := fun a => sub_nonneg.2 (min_le_left _ _)
  have hq0 : ∀ a, 0 ≤ q a - min (p a) (q a) := fun a => sub_nonneg.2 (min_le_right _ _)
  have hpt : ∀ a, (p a - min (p a) (q a)) * t / t = p a - min (p a) (q a) := fun a => by
    by_cases h : t = 0
    · have h1 := Finset.single_le_sum (f := fun a => p a - min (p a) (q a))
        (fun a _ => hp0 a) (Finset.mem_univ a)
      simp only [hsp, h] at h1
      rw [le_antisymm h1 (hp0 a), zero_mul, zero_div]
    · field_simp
  have hqt : ∀ b, (q b - min (p b) (q b)) * t / t = q b - min (p b) (q b) := fun b => by
    by_cases h : t = 0
    · have h1 := Finset.single_le_sum (f := fun a => q a - min (p a) (q a))
        (fun a _ => hq0 a) (Finset.mem_univ b)
      simp only [hsq, h] at h1
      rw [le_antisymm h1 (hq0 b), zero_mul, zero_div]
    · field_simp
  refine ⟨fun x => (if x.1 = x.2 then min (p x.1) (q x.1) else 0) +
      (p x.1 - min (p x.1) (q x.1)) * (q x.2 - min (p x.2) (q x.2)) / t, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x
    have ht0 : 0 ≤ t := ht ▸ tvDist_nonneg p q
    refine add_nonneg ?_ (div_nonneg (mul_nonneg (hp0 _) (hq0 _)) ht0)
    split_ifs
    · exact le_min (hp.nonneg _) (hq.nonneg _)
    · exact le_rfl
  · intro a
    show ∑ b, ((if a = b then min (p a) (q a) else 0) +
      (p a - min (p a) (q a)) * (q b - min (p b) (q b)) / t) = p a
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    have : ∑ b, (p a - min (p a) (q a)) * (q b - min (p b) (q b)) / t =
        p a - min (p a) (q a) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hsq, hpt]
    rw [this]; ring
  · intro b
    show ∑ a, ((if a = b then min (p a) (q a) else 0) +
      (p a - min (p a) (q a)) * (q b - min (p b) (q b)) / t) = q b
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    have : ∑ a, (p a - min (p a) (q a)) * (q b - min (p b) (q b)) / t =
        q b - min (p b) (q b) := by
      rw [← Finset.sum_div, ← Finset.sum_mul, hsp, mul_comm, hqt]
    rw [this]; ring
  · rw [Finset.sum_filter]
    have e : ∀ x : Ω × Ω, (if x.1 ≠ x.2 then (if x.1 = x.2 then min (p x.1) (q x.1) else 0) +
        (p x.1 - min (p x.1) (q x.1)) * (q x.2 - min (p x.2) (q x.2)) / t else 0) =
        (p x.1 - min (p x.1) (q x.1)) * (q x.2 - min (p x.2) (q x.2)) / t := fun x => by
      by_cases hx : x.1 = x.2
      · simp only [hx, ne_eq, not_true_eq_false, ↓reduceIte]
        rw [hzero, zero_div]
      · simp only [ne_eq, hx, not_false_eq_true, ↓reduceIte, zero_add]
    simp only [e]
    rw [← Finset.sum_div, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, hsq, ← Finset.sum_mul, hsp]
    exact mul_self_div_self t

section Markovian

variable [DecidableEq Ω] {P : Matrix Ω Ω ℝ}

/-- `Q` is a **Markovian coupling** of `P` with itself: row `(x, y)` couples `P x` and `P y`. -/
def IsMarkovianCoupling (Q : Matrix (Ω × Ω) (Ω × Ω) ℝ) (P : Matrix Ω Ω ℝ) : Prop :=
  ∀ w : Ω × Ω, IsCoupling (Q w) (P w.1) (P w.2)

omit [DecidableEq Ω] in
/-- One step of a Markovian coupling maps couplings of `μ, ν` to couplings of `μ P, ν P`. -/
theorem IsCoupling.vecMul {Q : Matrix (Ω × Ω) (Ω × Ω) ℝ} (hQ : IsMarkovianCoupling Q P)
    {r : Ω × Ω → ℝ} {μ ν : Ω → ℝ} (hr : IsCoupling r μ ν) :
    IsCoupling (r ᵥ* Q) (μ ᵥ* P) (ν ᵥ* P) := by
  refine ⟨fun z => Finset.sum_nonneg fun w _ => mul_nonneg (hr.nonneg w) ((hQ w).nonneg z),
    fun a => ?_, fun b => ?_⟩
  · simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hQ _).left]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, hr.left]
  · simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hQ _).right]
    rw [Fintype.sum_prod_type_right]
    simp only [← Finset.sum_mul, hr.right]

theorem IsCoupling.vecMul_pow {Q : Matrix (Ω × Ω) (Ω × Ω) ℝ} (hQ : IsMarkovianCoupling Q P)
    {r : Ω × Ω → ℝ} {μ ν : Ω → ℝ} (hr : IsCoupling r μ ν) (t : ℕ) :
    IsCoupling (r ᵥ* Q ^ t) (μ ᵥ* P ^ t) (ν ᵥ* P ^ t) := by
  induction t with
  | zero => simpa using hr
  | succ t ih =>
    simp only [pow_succ, ← Matrix.vecMul_vecMul]
    exact ih.vecMul hQ

/-- The **coupling bound for chains**: `tvDist (P^t x) (P^t y) ≤ P_{(x,y)}(X_t ≠ Y_t)` for a
Markovian coupling `Q`. -/
theorem tvDist_pow_row_le_coupling {Q : Matrix (Ω × Ω) (Ω × Ω) ℝ}
    (hQ : IsMarkovianCoupling Q P) (t : ℕ) (x y : Ω) :
    tvDist ((P ^ t) x) ((P ^ t) y) ≤ ∑ z with z.1 ≠ z.2, (Q ^ t) (x, y) z := by
  have h := (isCoupling_single x y).vecMul_pow hQ t
  simp only [single_one_vecMul, Matrix.row_apply'] at h
  exact h.tvDist_le

end Markovian

section Transport

variable {ρ : Ω → Ω → ℝ}

/-- `p` and `q` have a coupling of `ρ`-cost at most `c`. -/
def TransportLE (ρ : Ω → Ω → ℝ) (p q : Ω → ℝ) (c : ℝ) : Prop :=
  ∃ r : Ω × Ω → ℝ, IsCoupling r p q ∧ ∑ x, r x * ρ x.1 x.2 ≤ c

lemma TransportLE.mono {p q : Ω → ℝ} {c c' : ℝ} (h : TransportLE ρ p q c) (hc : c ≤ c') :
    TransportLE ρ p q c' :=
  let ⟨r, hr, hc'⟩ := h
  ⟨r, hr, hc'.trans hc⟩

lemma transportLE_self [DecidableEq Ω] {p : Ω → ℝ} (hp : ∀ a, 0 ≤ p a) (hρ : ∀ a, ρ a a = 0) :
    TransportLE ρ p p 0 := by
  refine ⟨_, isCoupling_diag hp, le_of_eq ?_⟩
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h
  · rw [h, hρ, mul_zero]
  · rw [zero_mul]

lemma transportLE_single [DecidableEq Ω] (a b : Ω) :
    TransportLE ρ (Pi.single a 1) (Pi.single b 1) (ρ a b) := by
  refine ⟨_, isCoupling_single a b, le_of_eq ?_⟩
  rw [Finset.sum_eq_single (a, b)]
  · simp
  · intro x _ hx
    rw [Pi.single_eq_of_ne hx, zero_mul]
  · simp

/-- **Gluing**: transport cost satisfies the triangle inequality. -/
theorem TransportLE.trans (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c)
    {p q s : Ω → ℝ} {c₁ c₂ : ℝ} (h₁ : TransportLE ρ p q c₁) (h₂ : TransportLE ρ q s c₂) :
    TransportLE ρ p s (c₁ + c₂) := by
  obtain ⟨r₁, hr₁, hc₁⟩ := h₁
  obtain ⟨r₂, hr₂, hc₂⟩ := h₂
  have hz : ∀ a b, q b = 0 → r₁ (a, b) = 0 := fun a b hb =>
    le_antisymm (hb ▸ hr₁.le_right a b) (hr₁.nonneg _)
  have hz' : ∀ b c, q b = 0 → r₂ (b, c) = 0 := fun b c hb =>
    le_antisymm (hb ▸ hr₂.le_left b c) (hr₂.nonneg _)
  have hq : ∀ b, 0 ≤ q b := fun b => hr₁.right b ▸ Finset.sum_nonneg fun a _ => hr₁.nonneg _
  let T : Ω → Ω → Ω → ℝ := fun a b c => r₁ (a, b) * r₂ (b, c) / q b
  have hT : ∀ a b c, 0 ≤ T a b c := fun a b c =>
    div_nonneg (mul_nonneg (hr₁.nonneg _) (hr₂.nonneg _)) (hq b)
  have F1 : ∀ a b, ∑ c, T a b c = r₁ (a, b) := fun a b => by
    simp only [T, ← Finset.sum_div, ← Finset.mul_sum, hr₂.left]
    by_cases hb : q b = 0
    · rw [hz a b hb, zero_mul, zero_div]
    · field_simp
  have F2 : ∀ b c, ∑ a, T a b c = r₂ (b, c) := fun b c => by
    simp only [T, ← Finset.sum_div, ← Finset.sum_mul, hr₁.right]
    by_cases hb : q b = 0
    · rw [hz' b c hb, mul_zero, zero_div]
    · field_simp
  refine ⟨fun x => ∑ b, T x.1 b x.2, ⟨fun x => Finset.sum_nonneg fun b _ => hT _ _ _,
    fun a => ?_, fun c => ?_⟩, ?_⟩
  · show ∑ c, ∑ b, T a b c = p a
    rw [Finset.sum_comm]
    simp only [F1, hr₁.left]
  · show ∑ a, ∑ b, T a b c = s c
    rw [Finset.sum_comm]
    simp only [F2, hr₂.right]
  · have S1 : ∑ a, ∑ c, ∑ b, T a b c * ρ a b = ∑ x, r₁ x * ρ x.1 x.2 :=
      calc ∑ a, ∑ c, ∑ b, T a b c * ρ a b = ∑ a, ∑ b, ∑ c, T a b c * ρ a b :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ a, ∑ b, r₁ (a, b) * ρ a b := Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b _ => by rw [← Finset.sum_mul, F1]
        _ = ∑ x, r₁ x * ρ x.1 x.2 :=
            (Fintype.sum_prod_type fun x : Ω × Ω => r₁ x * ρ x.1 x.2).symm
    have S2 : ∑ a, ∑ c, ∑ b, T a b c * ρ b c = ∑ x, r₂ x * ρ x.1 x.2 :=
      calc ∑ a, ∑ c, ∑ b, T a b c * ρ b c = ∑ c, ∑ a, ∑ b, T a b c * ρ b c := Finset.sum_comm
        _ = ∑ c, ∑ b, ∑ a, T a b c * ρ b c := Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = ∑ b, ∑ c, ∑ a, T a b c * ρ b c := Finset.sum_comm
        _ = ∑ b, ∑ c, r₂ (b, c) * ρ b c := Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => by rw [← Finset.sum_mul, F2]
        _ = ∑ x, r₂ x * ρ x.1 x.2 :=
            (Fintype.sum_prod_type fun x : Ω × Ω => r₂ x * ρ x.1 x.2).symm
    calc ∑ x : Ω × Ω, (∑ b, T x.1 b x.2) * ρ x.1 x.2
        = ∑ a, ∑ c, ∑ b, T a b c * ρ a c := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_mul]
      _ ≤ ∑ a, ∑ c, ∑ b, (T a b c * ρ a b + T a b c * ρ b c) := by
          refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
            Finset.sum_le_sum fun b _ => ?_
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (htri a b c) (hT a b c)
      _ = ∑ x, r₁ x * ρ x.1 x.2 + ∑ x, r₂ x * ρ x.1 x.2 := by
          simp only [Finset.sum_add_distrib, S1, S2]
      _ ≤ c₁ + c₂ := add_le_add hc₁ hc₂

/-- Transport cost contracts under a kernel that contracts it on each pair of states. -/
theorem TransportLE.vecMul {K : Matrix Ω Ω ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ a b, TransportLE ρ (K a) (K b) (κ * ρ a b)) {μ ν : Ω → ℝ} {c : ℝ}
    (h : TransportLE ρ μ ν c) : TransportLE ρ (μ ᵥ* K) (ν ᵥ* K) (κ * c) := by
  obtain ⟨r, hr, hc⟩ := h
  have hK' : ∀ w : Ω × Ω, ∃ R : Ω × Ω → ℝ, IsCoupling R (K w.1) (K w.2) ∧
      ∑ x, R x * ρ x.1 x.2 ≤ κ * ρ w.1 w.2 := fun w => hK w.1 w.2
  choose R hR hRc using hK'
  refine ⟨fun z => ∑ w, r w * R w z, ⟨fun z => Finset.sum_nonneg fun w _ =>
    mul_nonneg (hr.nonneg w) ((hR w).nonneg z), fun a => ?_, fun b => ?_⟩, ?_⟩
  · show ∑ b, ∑ w, r w * R w (a, b) = (μ ᵥ* K) a
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hR _).left]
    rw [Fintype.sum_prod_type]
    simp only [← Finset.sum_mul, hr.left]
    rfl
  · show ∑ a, ∑ w, r w * R w (a, b) = (ν ᵥ* K) b
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hR _).right]
    rw [Fintype.sum_prod_type_right]
    simp only [← Finset.sum_mul, hr.right]
    rfl
  · calc ∑ z, (∑ w, r w * R w z) * ρ z.1 z.2 = ∑ w, r w * ∑ z, R w z * ρ z.1 z.2 := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp only [mul_assoc]
      _ ≤ ∑ w, r w * (κ * ρ w.1 w.2) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hRc w) (hr.nonneg w)
      _ = κ * ∑ w, r w * ρ w.1 w.2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ κ * c := mul_le_mul_of_nonneg_left hc hκ

/-- Contraction on edges extends along a path, with the path's `ρ`-length as cost. -/
theorem transportLE_of_pathEdges [DecidableEq Ω] {K : Matrix Ω Ω ℝ} {κ : ℝ}
    (hK0 : ∀ a b, 0 ≤ K a b) (hρ : ∀ a, ρ a a = 0)
    (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c) {E : Ω → Ω → Prop}
    (hE : ∀ a b, E a b → TransportLE ρ (K a) (K b) (κ * ρ a b)) (a : Ω) (l : List Ω)
    (hl : ∀ e ∈ pathEdges (a :: l), E e.1 e.2) :
    TransportLE ρ (K a) (K ((a :: l).getLast (List.cons_ne_nil a l)))
      (κ * ((pathEdges (a :: l)).map fun e => ρ e.1 e.2).sum) := by
  induction l generalizing a with
  | nil => simpa [pathEdges] using transportLE_self (hK0 a) hρ
  | cons b l ih =>
    have hab : E a b := hl (a, b) (by simp [pathEdges])
    have hrest : ∀ e ∈ pathEdges (b :: l), E e.1 e.2 := fun e he =>
      hl e (by rw [pathEdges]; exact List.mem_cons_of_mem _ he)
    have h := (hE a b hab).trans htri (ih b hrest)
    rw [List.getLast_cons (List.cons_ne_nil b l)]
    simp only [pathEdges, List.map_cons, List.sum_cons]
    rw [mul_add]
    exact h

/-- Transport cost contracts by `κ ^ t` under `K ^ t`. -/
theorem TransportLE.vecMul_pow [DecidableEq Ω] {K : Matrix Ω Ω ℝ} {κ : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ a b, TransportLE ρ (K a) (K b) (κ * ρ a b)) {μ ν : Ω → ℝ} {c : ℝ}
    (h : TransportLE ρ μ ν c) (t : ℕ) : TransportLE ρ (μ ᵥ* K ^ t) (ν ᵥ* K ^ t) (κ ^ t * c) := by
  induction t with
  | zero => simpa using h
  | succ t ih =>
    simp only [pow_succ, ← Matrix.vecMul_vecMul]
    rw [show κ ^ t * κ * c = κ * (κ ^ t * c) by ring]
    exact ih.vecMul hκ hK

/-- Total variation is at most transport cost when `ρ ≥ 1` off the diagonal. -/
theorem tvDist_le_of_transportLE [DecidableEq Ω] (hρ0 : ∀ a b, 0 ≤ ρ a b)
    (hρ1 : ∀ a b, a ≠ b → 1 ≤ ρ a b) {p q : Ω → ℝ} {c : ℝ} (h : TransportLE ρ p q c) :
    tvDist p q ≤ c := by
  obtain ⟨r, hr, hc⟩ := h
  refine hr.tvDist_le.trans (le_trans ?_ hc)
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with hx
  · exact le_mul_of_one_le_right (hr.nonneg x) (hρ1 _ _ hx)
  · exact mul_nonneg (hr.nonneg x) (hρ0 _ _)

lemma one_sub_pow_le_exp_neg_mul {α : ℝ} (hα : α ≤ 1) (t : ℕ) :
    (1 - α) ^ t ≤ Real.exp (-(α * t)) := by
  rw [show -(α * t) = (t : ℝ) * -α by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-α)]) t

section PathCoupling

variable [DecidableEq Ω] {K : Matrix Ω Ω ℝ} {κ : ℝ} {E : Ω → Ω → Prop} {path : Ω → Ω → List Ω}

/-- Under the path-coupling hypotheses every pair contracts. -/
theorem transportLE_of_pathCoupling (hK0 : ∀ a b, 0 ≤ K a b) (hκ : 0 ≤ κ)
    (hρ : ∀ a, ρ a a = 0) (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c)
    (hE : ∀ a b, E a b → TransportLE ρ (K a) (K b) (κ * ρ a b))
    (hhead : ∀ x y, (path x y).head? = some x) (hlast : ∀ x y, (path x y).getLast? = some y)
    (hedge : ∀ x y, ∀ e ∈ pathEdges (path x y), E e.1 e.2)
    (hlen : ∀ x y, ((pathEdges (path x y)).map fun e => ρ e.1 e.2).sum ≤ ρ x y) (x y : Ω) :
    TransportLE ρ (K x) (K y) (κ * ρ x y) := by
  obtain ⟨l, hl⟩ : ∃ l, path x y = x :: l := by
    have h := hhead x y
    cases hp : path x y with
    | nil => rw [hp] at h; simp at h
    | cons z l =>
      rw [hp, List.head?_cons, Option.some.injEq] at h
      exact ⟨l, by rw [h]⟩
  have hly : (x :: l).getLast (List.cons_ne_nil x l) = y := by
    have h := hlast x y
    rw [hl, List.getLast?_eq_some_getLast (List.cons_ne_nil x l), Option.some.injEq] at h
    exact h
  have hedge' : ∀ e ∈ pathEdges (x :: l), E e.1 e.2 := fun e he =>
    hedge x y e (by rw [hl]; exact he)
  have hlen' : ((pathEdges (x :: l)).map fun e => ρ e.1 e.2).sum ≤ ρ x y := by
    have h := hlen x y
    rwa [hl] at h
  have h := transportLE_of_pathEdges hK0 hρ htri hE x l hedge'
  rw [hly] at h
  exact h.mono (mul_le_mul_of_nonneg_left hlen' hκ)

/-- **Path coupling** (Bubley–Dyer): `tvDist (K^t x) (K^t y) ≤ κ^t ρ(x, y)`. -/
theorem tvDist_pow_row_le_of_pathCoupling (hK0 : ∀ a b, 0 ≤ K a b) (hκ : 0 ≤ κ)
    (hρ0 : ∀ a b, 0 ≤ ρ a b) (hρ : ∀ a, ρ a a = 0) (hρ1 : ∀ a b, a ≠ b → 1 ≤ ρ a b)
    (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c)
    (hE : ∀ a b, E a b → TransportLE ρ (K a) (K b) (κ * ρ a b))
    (hhead : ∀ x y, (path x y).head? = some x) (hlast : ∀ x y, (path x y).getLast? = some y)
    (hedge : ∀ x y, ∀ e ∈ pathEdges (path x y), E e.1 e.2)
    (hlen : ∀ x y, ((pathEdges (path x y)).map fun e => ρ e.1 e.2).sum ≤ ρ x y)
    (t : ℕ) (x y : Ω) : tvDist ((K ^ t) x) ((K ^ t) y) ≤ κ ^ t * ρ x y := by
  have hK := transportLE_of_pathCoupling hK0 hκ hρ htri hE hhead hlast hedge hlen
  have h := (transportLE_single (ρ := ρ) x y).vecMul_pow hκ hK t
  simp only [single_one_vecMul, Matrix.row_apply'] at h
  exact tvDist_le_of_transportLE hρ0 hρ1 h

/-- **Path coupling** towards a stationary law: `tvDist (K^t x) π ≤ κ^t D` when
`∑ y, π y ρ(x, y) ≤ D`. -/
theorem tvDist_pow_row_stationary_le_of_pathCoupling (hK0 : ∀ a b, 0 ≤ K a b) (hκ : 0 ≤ κ)
    (hρ0 : ∀ a b, 0 ≤ ρ a b) (hρ : ∀ a, ρ a a = 0) (hρ1 : ∀ a b, a ≠ b → 1 ≤ ρ a b)
    (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c)
    (hE : ∀ a b, E a b → TransportLE ρ (K a) (K b) (κ * ρ a b))
    (hhead : ∀ x y, (path x y).head? = some x) (hlast : ∀ x y, (path x y).getLast? = some y)
    (hedge : ∀ x y, ∀ e ∈ pathEdges (path x y), E e.1 e.2)
    (hlen : ∀ x y, ((pathEdges (path x y)).map fun e => ρ e.1 e.2).sum ≤ ρ x y)
    {π : Ω → ℝ} (hπ : IsDistribution π) (hπK : π ᵥ* K = π) {D : ℝ}
    (hD : ∀ x, ∑ y, π y * ρ x y ≤ D) (t : ℕ) (x : Ω) :
    tvDist ((K ^ t) x) π ≤ κ ^ t * D := by
  have hK := transportLE_of_pathCoupling hK0 hκ hρ htri hE hhead hlast hedge hlen
  have h0 : TransportLE ρ (Pi.single x 1) π D := by
    refine ⟨fun z => (Pi.single x 1 : Ω → ℝ) z.1 * π z.2,
      isCoupling_prod (isDistribution_single x) hπ, ?_⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x]
    · simpa [mul_assoc] using hD x
    · intro b _ hb
      simp [hb]
    · simp
  have h := h0.vecMul_pow hκ hK t
  simp only [single_one_vecMul, Matrix.row_apply', vecMul_pow_eq_self hπK] at h
  exact tvDist_le_of_transportLE hρ0 hρ1 h

/-- **Path coupling**, exponential form with `κ = 1 - α`. -/
theorem tvDist_pow_row_le_exp_of_pathCoupling (hK0 : ∀ a b, 0 ≤ K a b) {α : ℝ} (hα : α ≤ 1)
    (hρ0 : ∀ a b, 0 ≤ ρ a b) (hρ : ∀ a, ρ a a = 0) (hρ1 : ∀ a b, a ≠ b → 1 ≤ ρ a b)
    (htri : ∀ a b c, ρ a c ≤ ρ a b + ρ b c)
    (hE : ∀ a b, E a b → TransportLE ρ (K a) (K b) ((1 - α) * ρ a b))
    (hhead : ∀ x y, (path x y).head? = some x) (hlast : ∀ x y, (path x y).getLast? = some y)
    (hedge : ∀ x y, ∀ e ∈ pathEdges (path x y), E e.1 e.2)
    (hlen : ∀ x y, ((pathEdges (path x y)).map fun e => ρ e.1 e.2).sum ≤ ρ x y)
    (t : ℕ) (x y : Ω) : tvDist ((K ^ t) x) ((K ^ t) y) ≤ Real.exp (-(α * t)) * ρ x y :=
  (tvDist_pow_row_le_of_pathCoupling hK0 (by linarith) hρ0 hρ hρ1 htri hE hhead hlast hedge
    hlen t x y).trans (mul_le_mul_of_nonneg_right (one_sub_pow_le_exp_neg_mul hα t) (hρ0 x y))

end PathCoupling

end Transport

end Couplings

end

end TheoremOS.Probability
