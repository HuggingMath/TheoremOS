import Submission.Library.TheoremOS.LinearAlgebra.PiTensor

/-!
# Pauli matrices and Pauli strings

The Pauli matrices `X, Y, Z` on `Fin 2`, the Pauli basis `pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ`
(`σ₀ = 1, σ₁ = X, σ₂ = Y, σ₃ = Z`) and the Pauli strings `pauliString s = ⨂ i, σ_{s i}` on
`ι → Fin 2`. Contents: the multiplication table, `σ² = 1`, Hermitian and unitary, traces,
trace orthogonality `tr (σ_a σ_b) = 2 δ_ab` and its `2 ^ |ι|` analogue for strings, the
completeness relation, the expansion `A = 2⁻ⁿ ∑ s, tr (P_s A) P_s` of every matrix, linear
independence of the strings, and the commute/anticommute sign of two strings.

Sources: M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
University Press, 2000, Section 2.1.3 (Pauli matrices), Exercise 2.35 and Section 8.3 (operator
expansion in the Pauli basis), Section 10.5.1 (the Pauli group: elements commute or anticommute).
Textbook material; nothing here is specific to a benchmark problem.

Bridges: with `Bit := Fin 2` and `Word N := Fin N → Bit`, an operator on `N` qubits is a
`Matrix (Fin N → Fin 2) (Fin N → Fin 2) ℂ`, the index type of `pauliString (s : Fin N → Fin 4)`.
A family of matrices satisfying a completeness relation gives an expansion by
`eq_sum_trace_smul_of_completeness`.
-/

namespace TheoremOS.LinearAlgebra

open Finset Matrix Complex
open scoped BigOperators

noncomputable section

/-- Pauli `X`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli `Z`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The Pauli basis `σ₀ = 1, σ₁ = X, σ₂ = Y, σ₃ = Z`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ := ![1, pauliX, pauliY, pauliZ]

@[simp] lemma pauli_zero : pauli 0 = 1 := rfl
@[simp] lemma pauli_one : pauli 1 = pauliX := rfl
@[simp] lemma pauli_two : pauli 2 = pauliY := rfl
@[simp] lemma pauli_three : pauli 3 = pauliZ := rfl

lemma pauli_apply (a : Fin 4) (i j : Fin 2) :
    pauli a i j = ![![![1, 0], ![0, 1]], ![![0, 1], ![1, 0]], ![![0, -I], ![I, 0]],
      ![![1, 0], ![0, -1]]] a i j := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, one_apply]

/-! ### The multiplication table -/

@[simp] lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, mul_apply, Fin.sum_univ_two, one_apply]

@[simp] lemma pauliY_mul_self : pauliY * pauliY = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliY, mul_apply, Fin.sum_univ_two, one_apply]

@[simp] lemma pauliZ_mul_self : pauliZ * pauliZ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, mul_apply, Fin.sum_univ_two, one_apply]

lemma pauliX_mul_pauliY : pauliX * pauliY = I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

lemma pauliY_mul_pauliX : pauliY * pauliX = -I • pauliZ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

lemma pauliY_mul_pauliZ : pauliY * pauliZ = I • pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

lemma pauliZ_mul_pauliY : pauliZ * pauliY = -I • pauliX := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

lemma pauliZ_mul_pauliX : pauliZ * pauliX = I • pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

lemma pauliX_mul_pauliZ : pauliX * pauliZ = -I • pauliY := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliX, pauliY, pauliZ, mul_apply, Fin.sum_univ_two]

@[simp] lemma pauli_mul_self (a : Fin 4) : pauli a * pauli a = 1 := by
  fin_cases a <;> simp

lemma isHermitian_pauliX : pauliX.IsHermitian :=
  IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [pauliX]

lemma isHermitian_pauliY : pauliY.IsHermitian :=
  IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [pauliY]

lemma isHermitian_pauliZ : pauliZ.IsHermitian :=
  IsHermitian.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [pauliZ]

lemma isHermitian_pauli (a : Fin 4) : (pauli a).IsHermitian := by
  fin_cases a
  · exact isHermitian_one
  · exact isHermitian_pauliX
  · exact isHermitian_pauliY
  · exact isHermitian_pauliZ

lemma pauli_mem_unitaryGroup (a : Fin 4) : pauli a ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, (isHermitian_pauli a).eq, pauli_mul_self]

lemma trace_pauli (a : Fin 4) : (pauli a).trace = if a = 0 then 2 else 0 := by
  fin_cases a <;> simp [pauliX, pauliY, pauliZ, trace_fin_two]

/-- Trace orthogonality `tr (σ_a σ_b) = 2 δ_ab`. -/
theorem trace_pauli_mul_pauli (a b : Fin 4) :
    (pauli a * pauli b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauliX, pauliY, pauliZ, Matrix.trace, Fin.sum_univ_two, one_apply] <;> norm_num

/-- The completeness relation `∑ a, (σ_a)_ij (σ_a)_kl = 2 δ_il δ_jk`. -/
theorem sum_pauli_apply_mul (i j k l : Fin 2) :
    ∑ a, pauli a i j * pauli a k l = if i = l ∧ j = k then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_four, pauliX, pauliY, pauliZ, one_apply] <;> norm_num

/-! ### Expansion in a complete family -/

/-- If a family satisfies `∑ a, (B a)_ij (B a)_kl = c δ_il δ_jk` with `c ≠ 0`, every matrix is
`c⁻¹ ∑ a, tr (B a * A) • B a`. -/
theorem eq_sum_trace_smul_of_completeness {n α K : Type*} [Fintype n] [DecidableEq n] [Fintype α]
    [Field K] (B : α → Matrix n n K) {c : K} (hc : c ≠ 0)
    (hB : ∀ i j k l, ∑ a, B a i j * B a k l = if i = l ∧ j = k then c else 0)
    (A : Matrix n n K) : A = c⁻¹ • ∑ a, (B a * A).trace • B a := by
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.trace, Matrix.diag, mul_apply, smul_eq_mul]
  have key : ∑ a, (∑ k, ∑ l, B a k l * A l k) * B a x y = c * A x y := by
    calc ∑ a, (∑ k, ∑ l, B a k l * A l k) * B a x y
        = ∑ k, ∑ l, A l k * ∑ a, B a k l * B a x y := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = c * A x y := by
          simp only [hB, mul_ite, mul_zero, ite_and]
          simp [mul_comm]
  rw [key, inv_mul_cancel_left₀ hc]

theorem pauli_expansion (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A = (2 : ℂ)⁻¹ • ∑ a, (pauli a * A).trace • pauli a :=
  eq_sum_trace_smul_of_completeness pauli two_ne_zero sum_pauli_apply_mul A

/-! ### Pauli strings -/

/-- Signs of the Pauli commutation relations: `σ_a σ_b = pauliSign a b • σ_b σ_a`. -/
def pauliSign (a b : Fin 4) : ℂ := if a = 0 ∨ b = 0 ∨ a = b then 1 else -1

theorem pauli_mul_comm (a b : Fin 4) :
    pauli a * pauli b = pauliSign a b • (pauli b * pauli a) := by
  fin_cases a <;> fin_cases b <;>
    simp [pauliSign, pauliX_mul_pauliY, pauliY_mul_pauliX, pauliY_mul_pauliZ, pauliZ_mul_pauliY,
      pauliZ_mul_pauliX, pauliX_mul_pauliZ]

variable {ι : Type*} [Fintype ι]

/-- The Pauli string `⨂ i, σ_{s i}` on `ι → Fin 2`. -/
def pauliString (s : ι → Fin 4) : Matrix (ι → Fin 2) (ι → Fin 2) ℂ :=
  piTensor fun i => pauli (s i)

lemma pauliString_apply (s : ι → Fin 4) (x y : ι → Fin 2) :
    pauliString s x y = ∏ i, pauli (s i) (x i) (y i) := rfl

lemma isHermitian_pauliString (s : ι → Fin 4) : (pauliString s).IsHermitian :=
  isHermitian_piTensor fun _ => isHermitian_pauli _

variable [DecidableEq ι]

@[simp] lemma pauliString_zero : pauliString (0 : ι → Fin 4) = 1 := by
  simp [pauliString, piTensor_one]

@[simp] lemma pauliString_mul_self (s : ι → Fin 4) : pauliString s * pauliString s = 1 := by
  rw [pauliString, piTensor_mul]
  simp [piTensor_one]

lemma pauliString_mem_unitaryGroup (s : ι → Fin 4) :
    pauliString s ∈ unitaryGroup (ι → Fin 2) ℂ :=
  piTensor_mem_unitaryGroup fun _ => pauli_mem_unitaryGroup _

/-- Trace orthogonality of Pauli strings: `tr (P_s P_t) = 2 ^ |ι| δ_st`. -/
theorem trace_pauliString_mul (s t : ι → Fin 4) :
    (pauliString s * pauliString t).trace = if s = t then 2 ^ Fintype.card ι else 0 := by
  rw [pauliString, pauliString, piTensor_mul, trace_piTensor]
  simp only [trace_pauli_mul_pauli]
  rw [Fintype.prod_ite_zero]
  by_cases h : s = t
  · subst h
    simp
  · rw [ite_eq_right (fun hst => h (funext hst)), ite_eq_right h]

lemma trace_pauliString (s : ι → Fin 4) :
    (pauliString s).trace = if s = 0 then 2 ^ Fintype.card ι else 0 := by
  simpa [eq_comm] using trace_pauliString_mul 0 s

/-- The completeness relation for Pauli strings. -/
theorem sum_pauliString_apply_mul (x y z w : ι → Fin 2) :
    ∑ s : ι → Fin 4, pauliString s x y * pauliString s z w =
      if x = w ∧ y = z then 2 ^ Fintype.card ι else 0 := by
  calc ∑ s : ι → Fin 4, pauliString s x y * pauliString s z w
      = ∏ i, ∑ a, pauli a (x i) (y i) * pauli a (z i) (w i) := by
        rw [Fintype.prod_sum]
        simp [pauliString_apply, Finset.prod_mul_distrib]
    _ = _ := by
        simp only [sum_pauli_apply_mul]
        rw [Fintype.prod_ite_zero]
        by_cases h : x = w ∧ y = z
        · obtain ⟨rfl, rfl⟩ := h
          simp
        · rw [ite_eq_right h, ite_eq_right]
          intro hi
          exact h ⟨funext fun i => (hi i).1, funext fun i => (hi i).2⟩

/-- Every operator on `ι → Fin 2` is `2⁻ⁿ ∑ s, tr (P_s A) P_s`. -/
theorem pauliString_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) :
    A = ((2 : ℂ) ^ Fintype.card ι)⁻¹ • ∑ s, (pauliString s * A).trace • pauliString s :=
  eq_sum_trace_smul_of_completeness pauliString (pow_ne_zero _ two_ne_zero)
    sum_pauliString_apply_mul A

theorem linearIndependent_pauliString : LinearIndependent ℂ (pauliString (ι := ι)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg s
  have h := congrArg (fun M => (pauliString s * M).trace) hg
  simp only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, trace_pauliString_mul,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    trace_zero] at h
  exact (mul_eq_zero.1 h).resolve_right (pow_ne_zero _ two_ne_zero)

/-- Two Pauli strings commute up to the product of the site signs. -/
theorem pauliString_mul_comm (s t : ι → Fin 4) :
    pauliString s * pauliString t =
      (∏ i, pauliSign (s i) (t i)) • (pauliString t * pauliString s) := by
  rw [pauliString, pauliString, piTensor_mul, piTensor_mul, ← piTensor_smul]
  congr 1
  funext i
  exact pauli_mul_comm _ _

omit [DecidableEq ι] in
/-- The sign is `-1` to the number of sites where the two strings anticommute. -/
lemma prod_pauliSign (s t : ι → Fin 4) :
    ∏ i, pauliSign (s i) (t i) =
      (-1) ^ (univ.filter fun i => s i ≠ 0 ∧ t i ≠ 0 ∧ s i ≠ t i).card := by
  have h : ∀ i, pauliSign (s i) (t i) = if s i ≠ 0 ∧ t i ≠ 0 ∧ s i ≠ t i then -1 else 1 := by
    intro i
    simp only [pauliSign]
    split_ifs <;> first | rfl | (exfalso; tauto)
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem pauliString_commute_or_anticommute (s t : ι → Fin 4) :
    pauliString s * pauliString t = pauliString t * pauliString s ∨
      pauliString s * pauliString t = -(pauliString t * pauliString s) := by
  rw [pauliString_mul_comm, prod_pauliSign]
  rcases neg_one_pow_eq_or ℂ (univ.filter fun i => s i ≠ 0 ∧ t i ≠ 0 ∧ s i ≠ t i).card with h | h
  · left; rw [h, one_smul]
  · right; rw [h, neg_one_smul]

end

end TheoremOS.LinearAlgebra
