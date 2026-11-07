import Submission.Library.TheoremOS.Probability.Dobrushin

/-!
# Reversible chains, Dirichlet forms and spectral gaps

A weight vector `π` and a kernel `P : Matrix Ω Ω ℝ` on a finite type; `P *ᵥ f` is the chain
acting on observables. Contents: the `π`-weighted product `piInner π f g = ∑ π f g`, the
Dirichlet form `dirichletForm π P f = ⟨f, f - P f⟩_π`, and the spectral gap in Poincaré form
`HasSpectralGap π P γ : ∀ f, γ · Var_π f ≤ E(f)`. Under detailed balance
`π x P x y = π y P y x` with unit row sums: `P` is self-adjoint for `⟨·,·⟩_π`; the edge form
`2 E(f) = ∑ π x P x y (f x - f y)²` and the pair form `2 Var_π f = ∑ π x π y (f x - f y)²`;
`E(f) ≥ 0`; a lazy kernel (`P x x ≥ 1/2`) is positive semidefinite and satisfies
Cauchy–Schwarz for `⟨u, P v⟩_π`. Consequences of a gap `γ` for a lazy reversible kernel:
`Var_π (P f) ≤ (1-γ)² Var_π f` and its iterate, the `L²` mixing bound
`‖P^t(x,·) - π‖_TV ≤ ½ (1-γ)^t √(1/π x - 1)` (for `γ ≤ 1`), the exponential form
`½ e^{-γt} √(1/π x - 1)` (any `γ`), and the uniform case `√N / 2 · e^{-γt}` for a symmetric
kernel. Bounding the gap: canonical paths (Diaconis–Stroock, Sinclair) — edge lists `Γ x y`
whose increments telescope and whose congestion
`∑ x, ∑ y, π x π y |Γ x y| · edgeMultiplicity (Γ x y) e ≤ B π a P a b` at every edge
`e = (a, b)` give `Var_π f ≤ B E(f)`, so gap `1/B`; paths may be given as vertex lists via
`pathEdges`; and the comparison of Dirichlet forms. Also `t`-step detailed balance and the
recursion bridge `k (t+1) x y = ∑ z, k t x z * P z y` ⟹ `k t = P ^ t`.

Sources: D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS, 2017,
§12.1–12.2 (spectral representation, relaxation time, `L²` bound), §13.2–13.4 (Dirichlet form,
spectral gap as a Poincaré constant, comparison, canonical paths); P. Diaconis and D. Stroock,
*Geometric bounds for eigenvalues of Markov chains*, Ann. Appl. Probab. 1 (1991) 36–61;
A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*,
Combin. Probab. Comput. 1 (1992) 351–370; P. Diaconis and L. Saloff-Coste, *Comparison
theorems for reversible Markov chains*, Ann. Appl. Probab. 3 (1993) 696–730. Textbook
material; nothing here is specific to a benchmark problem.

Bridges: an average `(∑ x, f x) / N` with `N = Fintype.card Ω` is
`expectation (uniform Ω) f` by `expectation_uniform`, so a uniform inner product or variance
written that way is `piInner (uniform Ω) f g` or `variance (uniform Ω) f`; an operator
`fun x => ∑ y, K x y * f y` is `K *ᵥ f` by `rfl`; a kernel power defined by recursion
`k 0 = 1`, `k (t+1) x y = ∑ z, k t x z * K z y` is `K ^ t` by `eq_pow_of_recursion`; a sum over
a `Finset` that is `Finset.univ` by definition (`allStates`) unfolds to `∑ x` first. The TV
distance of the row `(P ^ t) x` from `π` is `tvDist ((P ^ t) x) π`.
-/

namespace TheoremOS.Probability

open Finset Matrix
open TheoremOS.InformationTheory
open scoped BigOperators

noncomputable section

section Paths

variable {α : Type*}

/-- The consecutive pairs `(v₀, v₁), (v₁, v₂), …` of a vertex list. -/
def pathEdges : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: l => (a, b) :: pathEdges (b :: l)

/-- Increments along the edges of a vertex list telescope. -/
theorem sum_pathEdges (f : α → ℝ) (a : α) (l : List α) :
    ((pathEdges (a :: l)).map fun e => f e.2 - f e.1).sum =
      f ((a :: l).getLast (List.cons_ne_nil a l)) - f a := by
  induction l generalizing a with
  | nil => simp [pathEdges]
  | cons b l ih =>
    simp only [pathEdges, List.map_cons, List.sum_cons, ih, List.getLast_cons_cons]
    ring

theorem sum_pathEdges_of_head_last (f : α → ℝ) {l : List α} {x y : α}
    (hx : l.head? = some x) (hy : l.getLast? = some y) :
    ((pathEdges l).map fun e => f e.2 - f e.1).sum = f y - f x := by
  cases l with
  | nil => simp at hx
  | cons a l =>
    simp only [List.head?_cons, Option.some.injEq] at hx
    rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a l), Option.some.injEq] at hy
    rw [sum_pathEdges, hy, hx]

/-- Cauchy–Schwarz for a list: `(∑ aᵢ)² ≤ n ∑ aᵢ²`. -/
theorem sq_list_sum_le (l : List ℝ) : l.sum ^ 2 ≤ l.length * (l.map (· ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.map_cons, List.length_cons]
    push_cast
    have hQ : 0 ≤ (l.map (· ^ 2)).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
        exact sq_nonneg y
    by_cases hl : l = []
    · subst hl; simp
    have hn : (0 : ℝ) < l.length := by exact_mod_cast List.length_pos_of_ne_nil hl
    nlinarith [sq_nonneg ((l.length : ℝ) * a - l.sum), mul_le_mul_of_nonneg_left ih
      (by positivity : (0 : ℝ) ≤ l.length + 1)]

end Paths

variable {Ω : Type*} [Fintype Ω]

section Forms

/-- The `π`-weighted product `∑ x, π x * f x * g x`. -/
def piInner (π f g : Ω → ℝ) : ℝ := ∑ x, π x * f x * g x

/-- The Dirichlet form `⟨f, f - P f⟩_π`. -/
def dirichletForm (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) (f : Ω → ℝ) : ℝ :=
  piInner π f (fun x => f x - (P *ᵥ f) x)

/-- Spectral gap at least `γ`, in Poincaré form: `γ Var_π f ≤ E(f)` for every `f`. -/
def HasSpectralGap (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) (γ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, γ * variance π f ≤ dirichletForm π P f

lemma piInner_comm (π f g : Ω → ℝ) : piInner π f g = piInner π g f := by
  unfold piInner
  exact Finset.sum_congr rfl fun x _ => by ring

lemma piInner_self_nonneg {π : Ω → ℝ} (hπ : ∀ x, 0 ≤ π x) (f : Ω → ℝ) :
    0 ≤ piInner π f f :=
  Finset.sum_nonneg fun x _ => by rw [mul_assoc]; exact mul_nonneg (hπ x) (mul_self_nonneg _)

lemma dirichletForm_eq (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    dirichletForm π P f = piInner π f f - piInner π f (P *ᵥ f) := by
  simp only [dirichletForm, piInner, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- An average `(∑ x, f x) / N` is the expectation under the uniform distribution. -/
lemma expectation_uniform (f : Ω → ℝ) :
    expectation (uniform Ω) f = (∑ x, f x) / (Fintype.card Ω : ℝ) := by
  simp only [expectation, uniform, ← Finset.mul_sum]
  ring

lemma HasSpectralGap.mono {π : Ω → ℝ} (hπ : ∀ x, 0 ≤ π x) {P : Matrix Ω Ω ℝ} {γ γ' : ℝ}
    (h : HasSpectralGap π P γ) (hγ : γ' ≤ γ) : HasSpectralGap π P γ' := fun f =>
  (mul_le_mul_of_nonneg_right hγ (variance_nonneg hπ f)).trans (h f)

/-- **Comparison**: if `E_Q ≤ A E_P` and `Q` has gap `γ`, then `P` has gap `γ / A`. -/
theorem HasSpectralGap.of_dirichletForm_le {π : Ω → ℝ} {P Q : Matrix Ω Ω ℝ} {γ A : ℝ}
    (hA : 0 < A) (hQ : HasSpectralGap π Q γ)
    (hcmp : ∀ f, dirichletForm π Q f ≤ A * dirichletForm π P f) :
    HasSpectralGap π P (γ / A) := fun f => by
  rw [div_mul_eq_mul_div, div_le_iff₀ hA]
  linarith [hQ f, hcmp f, mul_comm A (dirichletForm π P f)]

lemma variance_eq_piInner {π g : Ω → ℝ} (hg : expectation π g = 0) :
    variance π g = piInner π g g := by
  unfold variance piInner
  rw [hg]
  simp only [expectation, sub_zero]
  exact Finset.sum_congr rfl fun x _ => by ring

lemma expectation_sub_const {π : Ω → ℝ} (hπ : IsDistribution π) (f : Ω → ℝ) (c : ℝ) :
    expectation π (fun x => f x - c) = expectation π f - c := by
  simp only [expectation, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.sum_eq_one,
    one_mul]

lemma variance_sub_const {π : Ω → ℝ} (hπ : IsDistribution π) (f : Ω → ℝ) (c : ℝ) :
    variance π (fun x => f x - c) = variance π f := by
  unfold variance
  rw [expectation_sub_const hπ f c]
  simp only [sub_sub_sub_cancel_right]

/-- Pair form of the variance: `2 Var_π f = ∑ x, ∑ y, π x π y (f x - f y)²`. -/
theorem two_mul_variance {π : Ω → ℝ} (hπ : IsDistribution π) (f : Ω → ℝ) :
    2 * variance π f = ∑ x, ∑ y, π x * π y * (f x - f y) ^ 2 := by
  have h : ∀ x y, π x * π y * (f x - f y) ^ 2 =
      π y * (π x * f x ^ 2) - 2 * (π x * f x) * (π y * f y) + π x * (π y * f y ^ 2) :=
    fun x y => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, hπ.sum_eq_one, one_mul]
  rw [variance_eq hπ]
  simp only [expectation]
  ring

end Forms

section Reversible

variable {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}

/-- Detailed balance with unit row sums makes `π` stationary. -/
lemma sum_mul_eq_of_detailedBalance (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (y : Ω) : ∑ x, π x * P x y = π y :=
  congrFun (vecMul_eq_of_detailedBalance hrow hrev) y

/-- A reversible kernel is self-adjoint for `⟨·,·⟩_π`. -/
theorem piInner_mulVec_comm (hrev : ∀ x y, π x * P x y = π y * P y x) (f g : Ω → ℝ) :
    piInner π f (P *ᵥ g) = piInner π (P *ᵥ f) g := by
  simp only [piInner, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    linear_combination f y * g x * hrev y x

/-- `∑ x, ∑ y, π x P x y (f x + c f y)² = (1 + c²) ⟨f, f⟩_π + 2c ⟨f, P f⟩_π`. -/
theorem sum_mul_add_smul_sq (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (f : Ω → ℝ) (c : ℝ) :
    ∑ x, ∑ y, π x * P x y * (f x + c * f y) ^ 2 =
      (1 + c ^ 2) * piInner π f f + 2 * c * piInner π f (P *ᵥ f) := by
  have h1 : ∑ x, ∑ y, π x * P x y * f x ^ 2 = piInner π f f := by
    unfold piInner
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, hrow x]
    ring
  have h2 : ∑ x, ∑ y, π x * P x y * (f x * f y) = piInner π f (P *ᵥ f) := by
    simp only [piInner, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have h3 : ∑ x, ∑ y, π x * P x y * f y ^ 2 = piInner π f f := by
    unfold piInner
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, sum_mul_eq_of_detailedBalance hrow hrev y]
    ring
  have split : ∀ x y, π x * P x y * (f x + c * f y) ^ 2 =
      π x * P x y * f x ^ 2 + 2 * c * (π x * P x y * (f x * f y)) +
        c ^ 2 * (π x * P x y * f y ^ 2) := fun x y => by ring
  simp only [split, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]
  ring

/-- **Edge form**: `2 E(f) = ∑ x, ∑ y, π x P x y (f x - f y)²`. -/
theorem two_mul_dirichletForm (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (f : Ω → ℝ) :
    2 * dirichletForm π P f = ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 := by
  have h := sum_mul_add_smul_sq hrow hrev f (-1)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  rw [h, dirichletForm_eq]
  ring

theorem dirichletForm_nonneg (hπ : ∀ x, 0 ≤ π x) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x) (f : Ω → ℝ) :
    0 ≤ dirichletForm π P f := by
  have h := two_mul_dirichletForm hrow hrev f
  have : 0 ≤ ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (hπ x) (hP x y)) (sq_nonneg _)
  linarith

/-- A lazy reversible kernel (`P x x ≥ 1/2`) is positive semidefinite for `⟨·,·⟩_π`. -/
theorem piInner_mulVec_nonneg (hπ : ∀ x, 0 ≤ π x) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) (f : Ω → ℝ) : 0 ≤ piInner π f (P *ᵥ f) := by
  have h := sum_mul_add_smul_sq hrow hrev f 1
  simp only [one_mul, one_pow, mul_one] at h
  have hdiag : ∀ x, π x * (2 * f x ^ 2) ≤ ∑ y, π x * P x y * (f x + f y) ^ 2 := fun x => by
    have hle := Finset.single_le_sum (f := fun y => π x * P x y * (f x + f y) ^ 2)
      (fun y _ => mul_nonneg (mul_nonneg (hπ x) (hP x y)) (sq_nonneg _)) (Finset.mem_univ x)
    have hx : π x * (2 * f x ^ 2) ≤ π x * P x x * (f x + f x) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left (hlazy x) (mul_nonneg (hπ x) (sq_nonneg (f x)))]
    exact hx.trans hle
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hdiag x
  have hval : ∑ x, π x * (2 * f x ^ 2) = 2 * piInner π f f := by
    simp only [piInner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  nlinarith

/-- **Cauchy–Schwarz** for the form `⟨u, P v⟩_π` of a lazy reversible kernel. -/
theorem sq_piInner_mulVec_le (hπ : ∀ x, 0 ≤ π x) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) (u v : Ω → ℝ) :
    piInner π u (P *ᵥ v) ^ 2 ≤ piInner π u (P *ᵥ u) * piInner π v (P *ᵥ v) := by
  have hsym : piInner π v (P *ᵥ u) = piInner π u (P *ᵥ v) := by
    rw [piInner_mulVec_comm hrev, piInner_comm]
  have hq : ∀ s : ℝ, 0 ≤ piInner π v (P *ᵥ v) * (s * s) + 2 * piInner π u (P *ᵥ v) * s +
      piInner π u (P *ᵥ u) := fun s => by
    have h0 := piInner_mulVec_nonneg hπ hP hrow hrev hlazy (u + s • v)
    have hexp : piInner π (u + s • v) (P *ᵥ (u + s • v)) = piInner π u (P *ᵥ u) +
        s * piInner π u (P *ᵥ v) + s * piInner π v (P *ᵥ u) +
          s * s * piInner π v (P *ᵥ v) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp only [piInner, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hexp, hsym] at h0
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

end Reversible

section Contraction

variable {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}

/-- A stationary `π` keeps expectations: `E_π (P f) = E_π f`. -/
lemma expectation_mulVec (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (f : Ω → ℝ) :
    expectation π (P *ᵥ f) = expectation π f := by
  change π ⬝ᵥ (P *ᵥ f) = π ⬝ᵥ f
  rw [Matrix.dotProduct_mulVec, vecMul_eq_of_detailedBalance hrow hrev]

lemma expectation_pow_mulVec [DecidableEq Ω] (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (t : ℕ) (f : Ω → ℝ) :
    expectation π (P ^ t *ᵥ f) = expectation π f := by
  change π ⬝ᵥ (P ^ t *ᵥ f) = π ⬝ᵥ f
  rw [Matrix.dotProduct_mulVec, vecMul_pow_eq_self (vecMul_eq_of_detailedBalance hrow hrev)]

/-- A gap `γ` contracts mean-zero functions: `‖P g‖²_π ≤ (1-γ)² ‖g‖²_π`. -/
theorem piInner_mulVec_self_le (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ} (hgap : HasSpectralGap π P γ) {g : Ω → ℝ}
    (hg : expectation π g = 0) :
    piInner π (P *ᵥ g) (P *ᵥ g) ≤ (1 - γ) ^ 2 * piInner π g g := by
  have hbound : ∀ h : Ω → ℝ, expectation π h = 0 →
      piInner π h (P *ᵥ h) ≤ (1 - γ) * piInner π h h := fun h hh => by
    have := hgap h
    rw [variance_eq_piInner hh, dirichletForm_eq] at this
    linarith
  have hPg : expectation π (P *ᵥ g) = 0 := by rw [expectation_mulVec hrow hrev, hg]
  have hX : piInner π g (P *ᵥ (P *ᵥ g)) = piInner π (P *ᵥ g) (P *ᵥ g) :=
    piInner_mulVec_comm hrev g (P *ᵥ g)
  have hcs := sq_piInner_mulVec_le hπ.nonneg hP hrow hrev hlazy g (P *ᵥ g)
  rw [hX] at hcs
  have hA := hbound g hg
  have hB := hbound (P *ᵥ g) hPg
  have hA0 := piInner_mulVec_nonneg hπ.nonneg hP hrow hrev hlazy g
  have hB0 := piInner_mulVec_nonneg hπ.nonneg hP hrow hrev hlazy (P *ᵥ g)
  have hX0 := piInner_self_nonneg hπ.nonneg (P *ᵥ g)
  have hG0 := piInner_self_nonneg hπ.nonneg g
  have hsq : piInner π (P *ᵥ g) (P *ᵥ g) ^ 2 ≤
      (1 - γ) ^ 2 * piInner π g g * piInner π (P *ᵥ g) (P *ᵥ g) :=
    calc _ ≤ _ := hcs
      _ ≤ ((1 - γ) * piInner π g g) * ((1 - γ) * piInner π (P *ᵥ g) (P *ᵥ g)) :=
          mul_le_mul hA hB hB0 (hA0.trans hA)
      _ = _ := by ring
  rcases hX0.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (sq_nonneg _) hG0
  · nlinarith

/-- **Variance contraction**: a gap `γ` for a lazy reversible kernel gives
`Var_π (P f) ≤ (1-γ)² Var_π f`. -/
theorem variance_mulVec_le (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ} (hgap : HasSpectralGap π P γ) (f : Ω → ℝ) :
    variance π (P *ᵥ f) ≤ (1 - γ) ^ 2 * variance π f := by
  obtain ⟨g, hgdef⟩ : ∃ g : Ω → ℝ, g = fun x => f x - expectation π f := ⟨_, rfl⟩
  have hg : expectation π g = 0 := by rw [hgdef, expectation_sub_const hπ, sub_self]
  have hPg : P *ᵥ g = fun x => (P *ᵥ f) x - expectation π f := by
    funext x
    simp only [hgdef, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hrow x, one_mul]
  have hPg0 : expectation π (P *ᵥ g) = 0 := by rw [expectation_mulVec hrow hrev, hg]
  have h1 : variance π (P *ᵥ f) = piInner π (P *ᵥ g) (P *ᵥ g) := by
    rw [← variance_eq_piInner hPg0, hPg, ← expectation_mulVec hrow hrev f,
      variance_sub_const hπ]
  have h2 : variance π f = piInner π g g := by
    rw [← variance_eq_piInner hg, hgdef, variance_sub_const hπ]
  rw [h1, h2]
  exact piInner_mulVec_self_le hπ hP hrow hrev hlazy hgap hg

theorem variance_pow_mulVec_le [DecidableEq Ω] (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ} (hgap : HasSpectralGap π P γ) (f : Ω → ℝ) (t : ℕ) :
    variance π (P ^ t *ᵥ f) ≤ ((1 - γ) ^ 2) ^ t * variance π f := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ' P t, ← Matrix.mulVec_mulVec]
    calc variance π (P *ᵥ (P ^ t *ᵥ f))
        ≤ (1 - γ) ^ 2 * variance π (P ^ t *ᵥ f) :=
          variance_mulVec_le hπ hP hrow hrev hlazy hgap _
      _ ≤ (1 - γ) ^ 2 * (((1 - γ) ^ 2) ^ t * variance π f) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ((1 - γ) ^ 2) ^ (t + 1) * variance π f := by ring

/-- `t`-step detailed balance. -/
theorem pow_detailedBalance [DecidableEq Ω] (hrev : ∀ x y, π x * P x y = π y * P y x)
    (t : ℕ) (x y : Ω) : π x * (P ^ t) x y = π y * (P ^ t) y x := by
  induction t generalizing x y with
  | zero =>
    rw [pow_zero]
    by_cases h : x = y
    · subst h; rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]
  | succ t ih =>
    have hl : π x * (P ^ (t + 1)) x y = ∑ z, π x * ((P ^ t) x z * P z y) := by
      rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    have hr : π y * (P ^ (t + 1)) y x = ∑ z, π y * (P y z * (P ^ t) z x) := by
      rw [pow_succ', Matrix.mul_apply, Finset.mul_sum]
    rw [hl, hr]
    exact Finset.sum_congr rfl fun z _ => by
      linear_combination P z y * ih x z + (P ^ t) z x * hrev z y

end Contraction

section Mixing

variable [DecidableEq Ω] {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}

/-- **`L²` mixing bound**: for a lazy reversible kernel with gap `γ ≤ 1`,
`‖P^t(x,·) - π‖_TV ≤ ½ (1-γ)^t √(1/π x - 1)`. -/
theorem tvDist_pow_row_le_of_spectralGap (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ} (hγ : γ ≤ 1) (hgap : HasSpectralGap π P γ)
    {x : Ω} (hx : 0 < π x) (t : ℕ) :
    tvDist ((P ^ t) x) π ≤ 1 / 2 * (1 - γ) ^ t * Real.sqrt (1 / π x - 1) := by
  obtain ⟨h0, hh0⟩ : ∃ h0 : Ω → ℝ, h0 = Pi.single x (1 / π x) := ⟨_, rfl⟩
  have hinv : π x * (1 / π x) = 1 := mul_one_div_cancel hx.ne'
  have hu : ∀ y, (P ^ t *ᵥ h0) y * π x = (P ^ t) y x := fun y => by
    simp only [hh0, Matrix.mulVec, dotProduct_single]
    rw [mul_assoc, one_div_mul_cancel hx.ne', mul_one]
  have hdiff : ∀ y, (P ^ t) x y - π y = π y * ((P ^ t *ᵥ h0) y - 1) := fun y => by
    have hb := pow_detailedBalance hrev t x y
    rw [← hu y] at hb
    have : π x * ((P ^ t) x y - π y * ((P ^ t *ᵥ h0) y - 1) - π y) = 0 := by
      linear_combination hb
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hx.ne'
    · linarith
  have hE0 : expectation π h0 = 1 := by
    change π ⬝ᵥ h0 = 1
    rw [hh0, dotProduct_single, hinv]
  have hsq : (fun ω => h0 ω ^ 2) = Pi.single x ((1 / π x) ^ 2) := by
    funext ω
    rw [hh0]
    by_cases h : ω = x
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hV0 : variance π h0 = 1 / π x - 1 := by
    rw [variance_eq hπ, hE0, hsq]
    change π ⬝ᵥ Pi.single x ((1 / π x) ^ 2) - 1 ^ 2 = 1 / π x - 1
    rw [dotProduct_single, sq, ← mul_assoc, hinv, one_mul, one_pow]
  have hEu : expectation π (P ^ t *ᵥ h0) = 1 := by
    rw [expectation_pow_mulVec hrow hrev, hE0]
  have hVu : variance π (P ^ t *ᵥ h0) ≤ ((1 - γ) ^ 2) ^ t * (1 / π x - 1) := by
    rw [← hV0]
    exact variance_pow_mulVec_le hπ hP hrow hrev hlazy hgap h0 t
  have hcs : expectation π (fun y => |(P ^ t *ᵥ h0) y - 1|) ≤
      Real.sqrt (variance π (P ^ t *ᵥ h0)) := by
    have h1 := sq_expectation_le hπ (fun y => |(P ^ t *ᵥ h0) y - 1|)
    have h2 : expectation π (fun y => |(P ^ t *ᵥ h0) y - 1| ^ 2) =
        variance π (P ^ t *ᵥ h0) := by
      simp only [variance, hEu, sq_abs]
    rw [h2] at h1
    exact (le_abs_self _).trans (Real.abs_le_sqrt h1)
  have habs : ∀ y, |(P ^ t) x y - π y| = π y * |(P ^ t *ᵥ h0) y - 1| := fun y => by
    rw [hdiff y, abs_mul, abs_of_nonneg (hπ.nonneg y)]
  have hct : 0 ≤ (1 - γ) ^ t := pow_nonneg (by linarith) t
  calc tvDist ((P ^ t) x) π = 1 / 2 * expectation π (fun y => |(P ^ t *ᵥ h0) y - 1|) := by
        simp only [tvDist, habs]
        rfl
    _ ≤ 1 / 2 * Real.sqrt (((1 - γ) ^ 2) ^ t * (1 / π x - 1)) := by
        gcongr
        exact hcs.trans (Real.sqrt_le_sqrt hVu)
    _ = 1 / 2 * (1 - γ) ^ t * Real.sqrt (1 / π x - 1) := by
        rw [← pow_mul, mul_comm 2 t, pow_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hct]
        ring

/-- Exponential form, for any gap `γ`: `‖P^t(x,·) - π‖_TV ≤ ½ e^{-γt} √(1/π x - 1)`. -/
theorem tvDist_pow_row_le_exp (hπ : IsDistribution π) (hP : ∀ x y, 0 ≤ P x y)
    (hrow : ∀ x, ∑ y, P x y = 1) (hrev : ∀ x y, π x * P x y = π y * P y x)
    (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ} (hgap : HasSpectralGap π P γ) {x : Ω}
    (hx : 0 < π x) (t : ℕ) :
    tvDist ((P ^ t) x) π ≤ 1 / 2 * Real.exp (-(γ * t)) * Real.sqrt (1 / π x - 1) := by
  rcases le_or_gt γ 1 with hγ | hγ
  · refine (tvDist_pow_row_le_of_spectralGap hπ hP hrow hrev hlazy hγ hgap hx t).trans ?_
    have h1 : (1 - γ) ^ t ≤ Real.exp (-(γ * t)) := by
      rw [show -(γ * t) = (t : ℝ) * -γ by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-γ)]) t
    gcongr
  · refine (tvDist_pow_row_le_of_spectralGap hπ hP hrow hrev hlazy le_rfl
      (hgap.mono hπ.nonneg hγ.le) hx t).trans ?_
    have h1 : (1 - 1 : ℝ) ^ t ≤ Real.exp (-(γ * t)) := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · rw [sub_self, zero_pow ht.ne']
        exact (Real.exp_pos _).le
    gcongr

/-- Uniform case: a lazy symmetric kernel with gap `γ` on `N` states has
`‖P^t(x,·) - uniform‖_TV ≤ √N / 2 · e^{-γt}`. -/
theorem tvDist_pow_row_uniform_le_exp (hP : ∀ x y, 0 ≤ P x y) (hrow : ∀ x, ∑ y, P x y = 1)
    (hsym : ∀ x y, P x y = P y x) (hlazy : ∀ x, 1 / 2 ≤ P x x) {γ : ℝ}
    (hgap : HasSpectralGap (uniform Ω) P γ) (x : Ω) (t : ℕ) :
    tvDist ((P ^ t) x) (uniform Ω) ≤
      Real.sqrt (Fintype.card Ω) / 2 * Real.exp (-(γ * t)) := by
  have : Nonempty Ω := ⟨x⟩
  have hx : 0 < uniform Ω x := by unfold uniform; positivity
  have hrev : ∀ x y, uniform Ω x * P x y = uniform Ω y * P y x := fun x y => by
    rw [hsym x y]
    simp only [uniform]
  have hN : Real.sqrt (1 / uniform Ω x - 1) ≤ Real.sqrt (Fintype.card Ω) := by
    apply Real.sqrt_le_sqrt
    simp only [uniform, one_div, inv_inv]
    linarith
  calc tvDist ((P ^ t) x) (uniform Ω)
      ≤ 1 / 2 * Real.exp (-(γ * t)) * Real.sqrt (1 / uniform Ω x - 1) :=
        tvDist_pow_row_le_exp isDistribution_uniform hP hrow hrev hlazy hgap hx t
    _ ≤ 1 / 2 * Real.exp (-(γ * t)) * Real.sqrt (Fintype.card Ω) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by ring

end Mixing

section CanonicalPaths

variable [DecidableEq Ω] {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}

omit [Fintype Ω] in
/-- Number of times the edge `e` occurs in the list `l`. -/
def edgeMultiplicity (l : List (Ω × Ω)) (e : Ω × Ω) : ℕ := l.countP fun e' => decide (e' = e)

lemma sum_map_eq_sum_edgeCount (l : List (Ω × Ω)) (D : Ω × Ω → ℝ) :
    (l.map D).sum = ∑ e, (edgeMultiplicity l e : ℝ) * D e := by
  induction l with
  | nil => simp [edgeMultiplicity]
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih, edgeMultiplicity, List.countP_cons,
      decide_eq_true_eq, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, add_mul,
      ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    ring

/-- **Canonical paths** (Diaconis–Stroock, Sinclair). Let `Γ x y` be a list of edges whose
increments telescope to `f y - f x`, and let the congestion of every edge `(a, b)` be at most
`B π a P a b`. Then `Var_π f ≤ B E(f)`. -/
theorem variance_le_of_paths (hπ : IsDistribution π) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (Γ : Ω → Ω → List (Ω × Ω)) (f : Ω → ℝ)
    (hΓ : ∀ x y, ((Γ x y).map fun e => f e.2 - f e.1).sum = f y - f x) {B : ℝ}
    (hB : ∀ e : Ω × Ω, ∑ x, ∑ y, π x * π y * (Γ x y).length * edgeMultiplicity (Γ x y) e ≤
      B * (π e.1 * P e.1 e.2)) :
    variance π f ≤ B * dirichletForm π P f := by
  have hpath : ∀ x y, (f x - f y) ^ 2 ≤ ∑ e, ((Γ x y).length : ℝ) *
      edgeMultiplicity (Γ x y) e * (f e.1 - f e.2) ^ 2 := fun x y => by
    have h := sq_list_sum_le ((Γ x y).map fun e => f e.2 - f e.1)
    rw [hΓ, List.length_map, List.map_map, sum_map_eq_sum_edgeCount, Finset.mul_sum] at h
    rw [← neg_sub, neg_sq]
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun e _ => ?_))
    simp only [Function.comp]
    ring
  have hswap : ∀ g : Ω → Ω → Ω × Ω → ℝ,
      ∑ x, ∑ y, ∑ e, g x y e = ∑ e, ∑ x, ∑ y, g x y e := fun g =>
    (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
  have hmain : ∑ x, ∑ y, π x * π y * (f x - f y) ^ 2 ≤
      B * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 := by
    calc ∑ x, ∑ y, π x * π y * (f x - f y) ^ 2
        ≤ ∑ x, ∑ y, ∑ e, π x * π y * (((Γ x y).length : ℝ) * edgeMultiplicity (Γ x y) e *
            (f e.1 - f e.2) ^ 2) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (hpath x y)
            (mul_nonneg (hπ.nonneg x) (hπ.nonneg y))
      _ = ∑ e, (∑ x, ∑ y, π x * π y * (Γ x y).length * edgeMultiplicity (Γ x y) e) *
            (f e.1 - f e.2) ^ 2 := by
          rw [hswap]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ ∑ e : Ω × Ω, B * (π e.1 * P e.1 e.2) * (f e.1 - f e.2) ^ 2 :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hB e) (sq_nonneg _)
      _ = B * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2 := by
          rw [Finset.mul_sum, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  have hV := two_mul_variance hπ f
  have hE := two_mul_dirichletForm hrow hrev f
  rw [← hV, ← hE] at hmain
  linarith

/-- Spectral gap from canonical paths with congestion `B`: gap at least `1 / B`. -/
theorem hasSpectralGap_of_paths (hπ : IsDistribution π) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (Γ : Ω → Ω → List (Ω × Ω))
    (hΓ : ∀ f : Ω → ℝ, ∀ x y, ((Γ x y).map fun e => f e.2 - f e.1).sum = f y - f x)
    {B : ℝ} (hBpos : 0 < B)
    (hB : ∀ e : Ω × Ω, ∑ x, ∑ y, π x * π y * (Γ x y).length * edgeMultiplicity (Γ x y) e ≤
      B * (π e.1 * P e.1 e.2)) :
    HasSpectralGap π P (1 / B) := fun f => by
  rw [one_div, inv_mul_le_iff₀ hBpos]
  exact variance_le_of_paths hπ hrow hrev Γ f (hΓ f) hB

/-- Canonical paths given as vertex lists from `x` to `y`. -/
theorem hasSpectralGap_of_vertexPaths (hπ : IsDistribution π) (hrow : ∀ x, ∑ y, P x y = 1)
    (hrev : ∀ x y, π x * P x y = π y * P y x) (path : Ω → Ω → List Ω)
    (hhead : ∀ x y, (path x y).head? = some x) (hlast : ∀ x y, (path x y).getLast? = some y)
    {B : ℝ} (hBpos : 0 < B)
    (hB : ∀ e : Ω × Ω, ∑ x, ∑ y, π x * π y * (pathEdges (path x y)).length *
      edgeMultiplicity (pathEdges (path x y)) e ≤ B * (π e.1 * P e.1 e.2)) :
    HasSpectralGap π P (1 / B) :=
  hasSpectralGap_of_paths hπ hrow hrev (fun x y => pathEdges (path x y))
    (fun f x y => sum_pathEdges_of_head_last f (hhead x y) (hlast x y)) hBpos hB

end CanonicalPaths

/-- A kernel power defined by recursion is the matrix power. -/
theorem eq_pow_of_recursion [DecidableEq Ω] (P : Matrix Ω Ω ℝ) (k : ℕ → Ω → Ω → ℝ)
    (h0 : ∀ x, k 0 x x = 1) (h0' : ∀ x y, x ≠ y → k 0 x y = 0)
    (hs : ∀ t x y, k (t + 1) x y = ∑ z, k t x z * P z y) (t : ℕ) (x y : Ω) :
    k t x y = (P ^ t) x y := by
  induction t generalizing y with
  | zero =>
    rw [pow_zero]
    by_cases h : x = y
    · subst h; rw [h0, Matrix.one_apply_eq]
    · rw [h0' x y h, Matrix.one_apply_ne h]
  | succ t ih =>
    rw [hs, pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun z _ => by rw [ih]

end

end TheoremOS.Probability
