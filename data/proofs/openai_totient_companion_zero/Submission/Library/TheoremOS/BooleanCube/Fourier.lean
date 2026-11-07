import Mathlib

/-!
# Fourier analysis on the Boolean cube

Functions `(ι → Bool) → ℝ` with the sign convention `false ↦ 1`, `true ↦ -1` and the uniform
average. The character of `S` is `χ_S x = ∏ i ∈ S, sign (x i)`; the Fourier coefficient is
`f̂ S = E[f · χ_S]`. Contents: character algebra and orthogonality, the Fourier expansion and its
uniqueness, Plancherel and Parseval, mean and variance, ±1-valued functions, and Fourier degree.

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014,
Chapter 1 (Theorem 1.1, Fact 1.6–1.9, Theorem 1.12, Proposition 1.13, Section 1.4). Textbook
material; nothing here is specific to a benchmark problem.

Bridges: a statement using `if b then 1 else -1` (true ↦ 1) is `-(sign b)`; a statement averaging
with `(Fintype.card α)⁻¹ * ∑` matches `average`; `Finset.univ.filter` degree definitions match
`degree` up to the decidable instance (use `classical` and `simp`).
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

/-- `false ↦ 1`, `true ↦ -1`. -/
def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] lemma sign_false : sign false = 1 := rfl
@[simp] lemma sign_true : sign true = -1 := rfl
@[simp] lemma sign_mul_self (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num [sign]
@[simp] lemma sign_sq (b : Bool) : sign b ^ 2 = 1 := by rw [sq, sign_mul_self]
@[simp] lemma abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
lemma sign_ne_zero (b : Bool) : sign b ≠ 0 := by cases b <;> norm_num [sign]
@[simp] lemma sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]
lemma sum_sign : ∑ b : Bool, sign b = 0 := by norm_num [sign]
lemma one_add_sign_mul_sign (a b : Bool) : 1 + sign a * sign b = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sign]

/-- The uniform average over a finite type. -/
def average {α : Type*} [Fintype α] (f : α → ℝ) : ℝ := (Fintype.card α : ℝ)⁻¹ * ∑ x, f x

section Average

variable {α : Type*} [Fintype α]

lemma average_add (f g : α → ℝ) : average (fun x => f x + g x) = average f + average g := by
  simp [average, sum_add_distrib, mul_add]

lemma average_sub (f g : α → ℝ) : average (fun x => f x - g x) = average f - average g := by
  simp [average, sum_sub_distrib, mul_sub]

lemma average_const_mul (c : ℝ) (f : α → ℝ) : average (fun x => c * f x) = c * average f := by
  simp only [average, ← mul_sum]; ring

lemma average_mul_const (c : ℝ) (f : α → ℝ) : average (fun x => f x * c) = average f * c := by
  simp only [average, ← sum_mul]; ring

lemma average_sum {β : Type*} (s : Finset β) (f : β → α → ℝ) :
    average (fun x => ∑ b ∈ s, f b x) = ∑ b ∈ s, average (f b) := by
  simp only [average, mul_sum]; rw [sum_comm]

lemma average_const [Nonempty α] (c : ℝ) : average (fun _ : α => c) = c := by
  have : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp [average, sum_const, card_univ, nsmul_eq_mul]

lemma average_nonneg {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ average f :=
  mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (sum_nonneg fun x _ => hf x)

lemma average_le_average {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g :=
  mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => h x) (inv_nonneg.2 (Nat.cast_nonneg _))

lemma average_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : average f = average g := by
  simp [average, h]

/-- Averages are invariant under a bijection of the domain. -/
lemma average_comp_equiv (e : α ≃ α) (f : α → ℝ) : average (fun x => f (e x)) = average f := by
  simp only [average, Equiv.sum_comp e f]

end Average

variable {ι : Type*}

/-- The character `χ_S x = ∏ i ∈ S, sign (x i)`. -/
def character (S : Finset ι) (x : ι → Bool) : ℝ := ∏ i ∈ S, sign (x i)

@[simp] lemma character_empty (x : ι → Bool) : character ∅ x = 1 := by simp [character]
@[simp] lemma character_singleton (i : ι) (x : ι → Bool) : character {i} x = sign (x i) := by simp [character]

lemma character_eq_prod_univ [Fintype ι] [DecidableEq ι] (S : Finset ι) (x : ι → Bool) :
    character S x = ∏ i, if i ∈ S then sign (x i) else 1 := by
  rw [character, prod_ite_mem_eq]

@[simp] lemma character_mul_self (S : Finset ι) (x : ι → Bool) : character S x * character S x = 1 := by
  rw [character, ← prod_mul_distrib]; simp

@[simp] lemma character_sq (S : Finset ι) (x : ι → Bool) : character S x ^ 2 = 1 := by
  rw [sq, character_mul_self]

@[simp] lemma abs_character (S : Finset ι) (x : ι → Bool) : |character S x| = 1 := by
  simp [character, abs_prod]

lemma character_ne_zero (S : Finset ι) (x : ι → Bool) : character S x ≠ 0 := by
  intro h; simpa [h] using character_mul_self S x

/-- `χ_S · χ_T = χ_{S ∆ T}`. -/
lemma character_mul [Fintype ι] [DecidableEq ι] (S T : Finset ι) (x : ι → Bool) :
    character S x * character T x = character (symmDiff S T) x := by
  rw [character_eq_prod_univ, character_eq_prod_univ, character_eq_prod_univ, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, mem_symmDiff]

lemma character_union_of_disjoint [DecidableEq ι] {S T : Finset ι} (h : Disjoint S T) (x : ι → Bool) :
    character (S ∪ T) x = character S x * character T x := by
  rw [character, prod_union h]; rfl

section Fourier

variable [Fintype ι] [DecidableEq ι]

/-- `∑ₓ χ_S x` is the size of the cube for `S = ∅` and zero otherwise. -/
lemma sum_character (S : Finset ι) :
    ∑ x : ι → Bool, character S x = if S = ∅ then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have key : ∑ x : ι → Bool, character S x = ∏ i : ι, ∑ b : Bool, (if i ∈ S then sign b else 1) := by
    rw [Fintype.prod_sum (fun (i : ι) (b : Bool) => if i ∈ S then sign b else 1)]
    exact sum_congr rfl fun x _ => character_eq_prod_univ S x
  rw [key]
  split_ifs with h
  · subst h; simp [Fintype.card_bool]
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 h
    exact prod_eq_zero (mem_univ i) (by simp [hi])

lemma average_character (S : Finset ι) : average (character S) = if S = ∅ then 1 else 0 := by
  rw [average, sum_character]
  split_ifs <;> simp

/-- Orthogonality of characters. -/
lemma average_character_mul (S T : Finset ι) :
    average (fun x => character S x * character T x) = if S = T then 1 else 0 := by
  simp only [character_mul, average_character]
  simp

/-- The Fourier coefficient `f̂ S = E[f · χ_S]`. -/
def fourierCoeff (f : (ι → Bool) → ℝ) (S : Finset ι) : ℝ := average fun x => f x * character S x

lemma fourierCoeff_empty (f : (ι → Bool) → ℝ) : fourierCoeff f ∅ = average f := by
  simp [fourierCoeff]

lemma fourierCoeff_add (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f x + g x) S = fourierCoeff f S + fourierCoeff g S := by
  simp only [fourierCoeff, add_mul, average_add]

lemma fourierCoeff_sub (f g : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => f x - g x) S = fourierCoeff f S - fourierCoeff g S := by
  simp only [fourierCoeff, sub_mul, average_sub]

lemma fourierCoeff_const_mul (c : ℝ) (f : (ι → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => c * f x) S = c * fourierCoeff f S := by
  simp only [fourierCoeff, mul_assoc, average_const_mul]

lemma fourierCoeff_character (S T : Finset ι) : fourierCoeff (character T) S = if T = S then 1 else 0 :=
  average_character_mul T S

/-- Uniqueness: the coefficients of an explicit character expansion are its weights. -/
lemma fourierCoeff_sum_character (c : Finset ι → ℝ) (S : Finset ι) :
    fourierCoeff (fun x => ∑ T, c T * character T x) S = c S := by
  simp only [fourierCoeff, sum_mul, mul_assoc, average_sum, average_const_mul, average_character_mul]
  simp

/-- `∑_S χ_S x χ_S y` is the size of the cube when `x = y` and zero otherwise. -/
lemma sum_character_mul_character (x y : ι → Bool) :
    ∑ S : Finset ι, character S x * character S y = if x = y then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  have key : ∑ S : Finset ι, character S x * character S y = ∏ i, (1 + sign (x i) * sign (y i)) := by
    rw [prod_one_add, powerset_univ]
    exact sum_congr rfl fun S _ => by rw [character, character, ← prod_mul_distrib]
  rw [key]
  simp only [one_add_sign_mul_sign]
  split_ifs with h
  · subst h; simp [Fintype.card_bool]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- Fourier expansion: `f = ∑_S f̂ S · χ_S`. -/
theorem fourier_expansion (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = ∑ S : Finset ι, fourierCoeff f S * character S x := by
  have hcard : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have : ∑ S : Finset ι, fourierCoeff f S * character S x =
      (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ y, f y * ∑ S : Finset ι, character S y * character S x := by
    simp only [fourierCoeff, average, mul_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun y _ => sum_congr rfl fun S _ => by ring
  rw [this]
  simp only [sum_character_mul_character, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  field_simp

/-- Two functions with the same Fourier coefficients are equal. -/
theorem eq_of_fourierCoeff_eq {f g : (ι → Bool) → ℝ} (h : ∀ S, fourierCoeff f S = fourierCoeff g S) : f = g := by
  funext x
  rw [fourier_expansion f x, fourier_expansion g x]
  simp [h]

/-- Plancherel: `E[f g] = ∑_S f̂ S ĝ S`. -/
theorem plancherel (f g : (ι → Bool) → ℝ) :
    average (fun x => f x * g x) = ∑ S : Finset ι, fourierCoeff f S * fourierCoeff g S := by
  conv_lhs => enter [1, x, 2]; rw [fourier_expansion g x]
  simp only [mul_sum, average_sum]
  refine sum_congr rfl fun S _ => ?_
  calc average (fun x => f x * (fourierCoeff g S * character S x))
      = average (fun x => f x * character S x * fourierCoeff g S) := average_congr fun x => by ring
    _ = fourierCoeff f S * fourierCoeff g S := by rw [average_mul_const]; rfl

/-- Parseval: `E[f²] = ∑_S f̂ S²`. -/
theorem parseval (f : (ι → Bool) → ℝ) :
    average (fun x => f x ^ 2) = ∑ S : Finset ι, fourierCoeff f S ^ 2 := by
  simpa [sq] using plancherel f f

/-- The variance `E[f²] - E[f]²`. -/
def variance (f : (ι → Bool) → ℝ) : ℝ := average (fun x => f x ^ 2) - average f ^ 2

theorem variance_eq_sum (f : (ι → Bool) → ℝ) :
    variance f = ∑ S ∈ univ.erase (∅ : Finset ι), fourierCoeff f S ^ 2 := by
  rw [variance, parseval, ← add_sum_erase _ _ (mem_univ (∅ : Finset ι)), fourierCoeff_empty]
  ring

lemma variance_nonneg (f : (ι → Bool) → ℝ) : 0 ≤ variance f := by
  rw [variance_eq_sum]; exact sum_nonneg fun S _ => sq_nonneg _

end Fourier

/-- `f` takes only the values `±1`. -/
def IsBooleanValued {α : Type*} (f : α → ℝ) : Prop := ∀ x, f x = 1 ∨ f x = -1

lemma IsBooleanValued.sq_eq_one {α : Type*} {f : α → ℝ} (hf : IsBooleanValued f) (x : α) : f x ^ 2 = 1 := by
  rcases hf x with h | h <;> simp [h]

lemma IsBooleanValued.abs_eq_one {α : Type*} {f : α → ℝ} (hf : IsBooleanValued f) (x : α) : |f x| = 1 := by
  rcases hf x with h | h <;> simp [h]

section Boolean

variable [Fintype ι] [DecidableEq ι]

/-- For ±1-valued `f`, the squared coefficients sum to one. -/
theorem IsBooleanValued.sum_fourierCoeff_sq {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) :
    ∑ S : Finset ι, fourierCoeff f S ^ 2 = 1 := by
  rw [← parseval, average_congr hf.sq_eq_one, average_const]

/-- Every coefficient of a function bounded by one is bounded by one. -/
lemma abs_fourierCoeff_le {f : (ι → Bool) → ℝ} {B : ℝ} (hf : ∀ x, |f x| ≤ B) (S : Finset ι) :
    |fourierCoeff f S| ≤ B := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hf (fun _ => false))
  unfold fourierCoeff average
  rw [abs_mul, abs_inv, Nat.abs_cast]
  have hcard : (0 : ℝ) < Fintype.card (ι → Bool) := Nat.cast_pos.2 Fintype.card_pos
  rw [inv_mul_le_iff₀ hcard]
  calc |∑ x, f x * character S x| ≤ ∑ x : ι → Bool, |f x * character S x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : ι → Bool, B := sum_le_sum fun x _ => by rw [abs_mul, abs_character, mul_one]; exact hf x
    _ = Fintype.card (ι → Bool) * B := by simp [sum_const, card_univ, nsmul_eq_mul]

lemma IsBooleanValued.abs_fourierCoeff_le_one {f : (ι → Bool) → ℝ} (hf : IsBooleanValued f) (S : Finset ι) :
    |fourierCoeff f S| ≤ 1 :=
  abs_fourierCoeff_le (fun x => (hf.abs_eq_one x).le) S

/-- Fourier degree: the largest `|S|` with `f̂ S ≠ 0` (zero for the zero function). -/
def degree (f : (ι → Bool) → ℝ) : ℕ := (univ.filter fun S : Finset ι => fourierCoeff f S ≠ 0).sup card

lemma card_le_degree {f : (ι → Bool) → ℝ} {S : Finset ι} (h : fourierCoeff f S ≠ 0) : S.card ≤ degree f :=
  le_sup (f := card) (mem_filter.2 ⟨mem_univ S, h⟩)

lemma fourierCoeff_eq_zero_of_degree_lt {f : (ι → Bool) → ℝ} {S : Finset ι} (h : degree f < S.card) :
    fourierCoeff f S = 0 := by
  by_contra hne; exact absurd (card_le_degree hne) (not_le.2 h)

lemma degree_le_iff {f : (ι → Bool) → ℝ} {d : ℕ} : degree f ≤ d ↔ ∀ S, fourierCoeff f S ≠ 0 → S.card ≤ d := by
  simp [degree, Finset.sup_le_iff]

/-- `f` equals its expansion over sets of size at most its degree. -/
theorem fourier_expansion_degree (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    f x = ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ degree f), fourierCoeff f S * character S x := by
  rw [fourier_expansion f x, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  split_ifs with h
  · rfl
  · rw [fourierCoeff_eq_zero_of_degree_lt (not_le.1 h), zero_mul]

lemma degree_character (S : Finset ι) : degree (character S) = S.card := by
  apply le_antisymm
  · rw [degree_le_iff]; intro T h
    rw [fourierCoeff_character] at h
    split_ifs at h with hT
    · exact hT ▸ le_rfl
    · exact absurd rfl h
  · exact card_le_degree (by simp [fourierCoeff_character])

end Boolean

end

end TheoremOS.BooleanCube
