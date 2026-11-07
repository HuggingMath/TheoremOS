import Submission.Library.TheoremOS.InformationTheory.Entropy

/-!
# Density matrices, measurements and partial traces

Finite-dimensional quantum probability over `𝕜 = ℝ` or `ℂ`. Contents: `0 ≤ tr (A B)` for
positive semidefinite `A, B` (with its real-part and monotone forms, and `tr (A B)` real for
Hermitian `A, B`); density matrices (`IsDensity ρ`: positive semidefinite, trace one) and their
closure under mixtures, Kronecker products, isometric conjugation and Kraus maps; the diagonal of a
density matrix as a distribution; POVMs (`IsPOVM E`: positive semidefinite, summing to `1`), the
Born rule `a ↦ re tr (E a ρ)` as a distribution, coarse-graining and Kronecker products of POVMs;
pure states `vecMulVec ψ (star ψ)` and the vector form `star ψ ⬝ᵥ (M *ᵥ ψ)` of the Born rule; the
partial traces `traceRight`, `traceLeft`, their trace, Kronecker, duality and positivity lemmas and
no-signalling; columns and rows of a unitary as distributions, and isometries preserving
`∑ normSq`.

Sources: M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
University Press, 2000, Sections 2.2.3–2.2.6 (POVMs, measurement statistics), 2.4 (density
operators, Theorem 2.5), 2.4.3 (partial trace), 8.2.3 (operator-sum representation); R. A. Horn
and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013, Section 7.1 and
Theorem 7.5.4 (trace of a product of positive semidefinite matrices). Textbook material; nothing
here is specific to a benchmark problem.

Bridges: these statements need `open scoped ComplexOrder` so that `PosSemidef` over `ℂ` makes
sense. A definition `IsState P := P.PosSemidef ∧ trace P = 1` is `IsDensity P` by `Iff.rfl`; a
structure with fields `(∀ a, (E a).PosSemidef)` and `∑ a, E a = 1` gives `IsPOVM E` by
`⟨pos, sum⟩`. Over `ℂ`, `RCLike.re` is `Complex.re` (`RCLike.re_to_complex`) and the unit-vector
hypothesis `∑ i, Complex.normSq (ψ i) = 1` gives `star ψ ⬝ᵥ ψ = 1` by
`star_dotProduct_self_eq_one`. A Born probability written entrywise,
`∑ i, ∑ j, (star (ψ i) * (A i.1 j.1 * B i.2 j.2) * ψ j).re`, is
`re (star ψ ⬝ᵥ ((A ⊗ₖ B) *ᵥ ψ))` by `sum_sum_re_star_mul_kronecker_mul`. Mathlib already has
`PosSemidef.kronecker`, `posSemidef_sum`, `PosSemidef.trace_nonneg`, `trace_kronecker` and
`posSemidef_vecMulVec_self_star`.
-/

namespace TheoremOS.LinearAlgebra

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open TheoremOS.InformationTheory

noncomputable section

variable {ι κ l m n : Type*}

section TraceProduct

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype n]

/-- `0 ≤ tr (A B)` for positive semidefinite `A` and `B`. -/
theorem trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ trace (A * B) := by
  classical
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [star_eq_conjTranspose, Matrix.mul_assoc, trace_mul_comm]
  exact (hB.mul_mul_conjTranspose_same y).trace_nonneg

theorem re_trace_mul_nonneg {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ RCLike.re (trace (A * B)) :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg hA hB)).1

/-- `tr (A B)` is real for Hermitian `A` and `B`. -/
theorem im_trace_mul_eq_zero {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    RCLike.im (trace (A * B)) = 0 := by
  rw [← RCLike.conj_eq_iff_im, ← RCLike.star_def, ← trace_conjTranspose, conjTranspose_mul,
    hA.eq, hB.eq, trace_mul_comm]

theorem ofReal_re_trace_mul {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (RCLike.re (trace (A * B)) : 𝕜) = trace (A * B) :=
  RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (im_trace_mul_eq_zero hA hB))

/-- `B ≤ C` in the Loewner order gives `tr (A B) ≤ tr (A C)` for positive semidefinite `A`. -/
theorem trace_mul_le_trace_mul {A B C : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hBC : (C - B).PosSemidef) : trace (A * B) ≤ trace (A * C) := by
  have := trace_mul_nonneg hA hBC
  rwa [Matrix.mul_sub, trace_sub, sub_nonneg] at this

theorem re_trace_mul_le_re_trace_mul {A B C : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hBC : (C - B).PosSemidef) : RCLike.re (trace (A * B)) ≤ RCLike.re (trace (A * C)) :=
  RCLike.re_le_re (trace_mul_le_trace_mul hA hBC)

theorem re_trace_mul_le_re_trace [DecidableEq n] {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : (1 - B).PosSemidef) : RCLike.re (trace (A * B)) ≤ RCLike.re (trace A) := by
  simpa using re_trace_mul_le_re_trace_mul hA hB

end TraceProduct

section Density

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

/-- A density matrix: positive semidefinite with trace one. -/
def IsDensity (ρ : Matrix n n 𝕜) : Prop := ρ.PosSemidef ∧ trace ρ = 1

lemma isDensity_iff {ρ : Matrix n n 𝕜} : IsDensity ρ ↔ ρ.PosSemidef ∧ trace ρ = 1 := Iff.rfl

namespace IsDensity

variable {ρ σ : Matrix n n 𝕜}

lemma posSemidef (h : IsDensity ρ) : ρ.PosSemidef := h.1

lemma trace_eq_one (h : IsDensity ρ) : trace ρ = 1 := h.2

lemma isHermitian (h : IsDensity ρ) : ρ.IsHermitian := h.1.isHermitian

/-- The diagonal of a density matrix is a probability distribution. -/
theorem isDistribution_diag (h : IsDensity ρ) : IsDistribution fun i => RCLike.re (ρ i i) where
  nonneg _ := (RCLike.nonneg_iff.mp h.1.diag_nonneg).1
  sum_eq_one := by
    have : ∑ i, ρ i i = trace ρ := rfl
    rw [← map_sum, this, h.2, RCLike.one_re]

/-- A mixture `∑ w i • ρ i` of density matrices with weights a distribution `w`. -/
theorem sum_smul [Fintype ι] {w : ι → ℝ} (hw : IsDistribution w) {ρ : ι → Matrix n n 𝕜}
    (hρ : ∀ i, IsDensity (ρ i)) : IsDensity (∑ i, (w i : 𝕜) • ρ i) := by
  refine ⟨posSemidef_sum _ fun i _ => (hρ i).1.smul (RCLike.ofReal_nonneg.mpr (hw.nonneg i)), ?_⟩
  simp only [trace_sum, trace_smul, (hρ _).2, smul_eq_mul, mul_one]
  exact_mod_cast hw.sum_eq_one

theorem kronecker {τ : Matrix m m 𝕜} (hρ : IsDensity ρ) (hτ : IsDensity τ) :
    IsDensity (ρ ⊗ₖ τ) :=
  ⟨hρ.1.kronecker hτ.1, by rw [trace_kronecker, hρ.2, hτ.2, mul_one]⟩

/-- Conjugation `V ρ Vᴴ` by an isometry `Vᴴ V = 1` (for example a unitary). -/
theorem conj_isometry [DecidableEq n] {V : Matrix m n 𝕜} (hV : Vᴴ * V = 1) (hρ : IsDensity ρ) :
    IsDensity (V * ρ * Vᴴ) :=
  ⟨hρ.1.mul_mul_conjTranspose_same V, by rw [trace_mul_cycle, hV, Matrix.one_mul, hρ.2]⟩

/-- A Kraus map `ρ ↦ ∑ K i ρ (K i)ᴴ` with `∑ (K i)ᴴ K i = 1` sends density matrices to density
matrices. -/
theorem sum_kraus [Fintype ι] [DecidableEq n] {K : ι → Matrix m n 𝕜}
    (hK : ∑ i, (K i)ᴴ * K i = 1) (hρ : IsDensity ρ) : IsDensity (∑ i, K i * ρ * (K i)ᴴ) := by
  refine ⟨posSemidef_sum _ fun i _ => hρ.1.mul_mul_conjTranspose_same (K i), ?_⟩
  rw [trace_sum, Finset.sum_congr rfl fun i _ => trace_mul_cycle (K i) ρ (K i)ᴴ, ← trace_sum,
    ← Finset.sum_mul, hK, Matrix.one_mul, hρ.2]

end IsDensity

end Density

section KroneckerSum

variable {p q R : Type*} [CommSemiring R]

theorem sum_kronecker (s : Finset ι) (A : ι → Matrix l m R) (B : Matrix n p R) :
    (∑ i ∈ s, A i) ⊗ₖ B = ∑ i ∈ s, A i ⊗ₖ B := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.sum_mul]

theorem kronecker_sum (A : Matrix l m R) (s : Finset ι) (B : ι → Matrix n p R) :
    A ⊗ₖ (∑ i ∈ s, B i) = ∑ i ∈ s, A ⊗ₖ B i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Finset.mul_sum]

theorem sum_kronecker_sum (s : Finset ι) (t : Finset κ) (A : ι → Matrix l m R)
    (B : κ → Matrix n p R) :
    (∑ i ∈ s, A i) ⊗ₖ (∑ j ∈ t, B j) = ∑ i ∈ s, ∑ j ∈ t, A i ⊗ₖ B j := by
  rw [sum_kronecker]
  simp_rw [kronecker_sum]

/-- Measuring a product state with a product observable factorizes. -/
theorem trace_kronecker_mul_kronecker [Fintype m] [Fintype n] (A ρ : Matrix m m R)
    (B σ : Matrix n n R) : trace ((A ⊗ₖ B) * (ρ ⊗ₖ σ)) = trace (A * ρ) * trace (B * σ) := by
  rw [← mul_kronecker_mul, trace_kronecker]

end KroneckerSum

section POVM

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype ι] [Fintype n] [DecidableEq n]

/-- A POVM: positive semidefinite effects summing to the identity. -/
structure IsPOVM (E : ι → Matrix n n 𝕜) : Prop where
  posSemidef : ∀ a, (E a).PosSemidef
  sum_eq_one : ∑ a, E a = 1

namespace IsPOVM

variable {E : ι → Matrix n n 𝕜}

omit [Fintype n] in
theorem one_sub_posSemidef [DecidableEq ι] (hE : IsPOVM E) (a : ι) : (1 - E a).PosSemidef := by
  rw [← hE.sum_eq_one, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_sub_cancel_left]
  exact posSemidef_sum _ fun b _ => hE.posSemidef b

/-- The Born rule: a POVM measured on a density matrix gives a probability distribution. -/
theorem isDistribution_re_trace_mul (hE : IsPOVM E) {ρ : Matrix n n 𝕜} (hρ : IsDensity ρ) :
    IsDistribution fun a => RCLike.re (trace (E a * ρ)) where
  nonneg a := re_trace_mul_nonneg (hE.posSemidef a) hρ.1
  sum_eq_one := by
    rw [← map_sum, ← trace_sum, ← Finset.sum_mul, hE.sum_eq_one, Matrix.one_mul, hρ.2,
      RCLike.one_re]

theorem re_trace_mul_le_one (hE : IsPOVM E) {ρ : Matrix n n 𝕜} (hρ : IsDensity ρ) (a : ι) :
    RCLike.re (trace (E a * ρ)) ≤ 1 :=
  (hE.isDistribution_re_trace_mul hρ).le_one a

omit [Fintype n] in
/-- Coarse-graining a POVM along `f : ι → κ`. -/
theorem fiberwise [Fintype κ] [DecidableEq κ] (hE : IsPOVM E) (f : ι → κ) :
    IsPOVM fun c => ∑ a ∈ univ.filter (f · = c), E a where
  posSemidef _ := posSemidef_sum _ fun a _ => hE.posSemidef a
  sum_eq_one := by rw [Finset.sum_fiberwise, hE.sum_eq_one]

theorem kronecker [Fintype κ] [Fintype m] [DecidableEq m] {F : κ → Matrix m m 𝕜} (hE : IsPOVM E)
    (hF : IsPOVM F) : IsPOVM fun ab : ι × κ => E ab.1 ⊗ₖ F ab.2 where
  posSemidef ab := (hE.posSemidef ab.1).kronecker (hF.posSemidef ab.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, ← sum_kronecker_sum, hE.sum_eq_one, hF.sum_eq_one,
      one_kronecker_one]

end IsPOVM

end POVM

section PureState

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype n]

/-- The trace of `M` against the pure state `ψ ψᴴ` is the quadratic form `ψᴴ M ψ`. -/
theorem trace_mul_vecMulVec_star (M : Matrix n n 𝕜) (ψ : n → 𝕜) :
    trace (M * vecMulVec ψ (star ψ)) = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

theorem isDensity_vecMulVec_star {ψ : n → 𝕜} (hψ : star ψ ⬝ᵥ ψ = 1) :
    IsDensity (vecMulVec ψ (star ψ)) :=
  ⟨posSemidef_vecMulVec_self_star ψ, by rw [trace_vecMulVec, dotProduct_comm, hψ]⟩

/-- An entrywise quadratic form `∑ i, ∑ j, star (ψ i) * M i j * ψ j` is `ψᴴ M ψ`. -/
theorem sum_sum_star_mul_mul (M : Matrix n n 𝕜) (ψ : n → 𝕜) :
    ∑ i, ∑ j, star (ψ i) * M i j * ψ j = star ψ ⬝ᵥ (M *ᵥ ψ) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

/-- The Born rule for a unit vector: `a ↦ re (ψᴴ E_a ψ)` is a probability distribution. -/
theorem IsPOVM.isDistribution_re_star_dotProduct [Fintype ι] [DecidableEq n]
    {E : ι → Matrix n n 𝕜} (hE : IsPOVM E) {ψ : n → 𝕜} (hψ : star ψ ⬝ᵥ ψ = 1) :
    IsDistribution fun a => RCLike.re (star ψ ⬝ᵥ (E a *ᵥ ψ)) := by
  simpa only [trace_mul_vecMulVec_star] using
    hE.isDistribution_re_trace_mul (isDensity_vecMulVec_star hψ)

end PureState

section Complex

variable [Fintype n]

/-- `∑ i, normSq (ψ i)` is `ψᴴ ψ`. -/
theorem ofReal_sum_normSq (ψ : n → ℂ) : ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) = star ψ ⬝ᵥ ψ := by
  simp [dotProduct, Complex.normSq_eq_conj_mul_self]

theorem star_dotProduct_self_eq_one {ψ : n → ℂ} (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    star ψ ⬝ᵥ ψ = 1 := by
  rw [← ofReal_sum_normSq, hψ, Complex.ofReal_one]

/-- The entrywise Born probability of a product observable `A ⊗ B` on a bipartite vector. -/
theorem sum_sum_re_star_mul_kronecker_mul [Fintype l] [Fintype m] (A : Matrix l l ℂ) (B : Matrix m m ℂ)
    (ψ : l × m → ℂ) :
    ∑ i, ∑ j, (star (ψ i) * (A i.1 j.1 * B i.2 j.2) * ψ j).re =
      (star ψ ⬝ᵥ ((A ⊗ₖ B) *ᵥ ψ)).re := by
  rw [← sum_sum_star_mul_mul, Complex.re_sum]
  simp only [Complex.re_sum]
  rfl

/-- Two POVMs measured on a bipartite unit vector give a joint distribution of outcomes. -/
theorem isDistribution_born_kronecker [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
    [Fintype ι] [Fintype κ] {A : ι → Matrix l l ℂ} {B : κ → Matrix m m ℂ} (hA : IsPOVM A)
    (hB : IsPOVM B) {ψ : l × m → ℂ} (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    IsDistribution fun ab : ι × κ =>
      ∑ i, ∑ j, (star (ψ i) * (A ab.1 i.1 j.1 * B ab.2 i.2 j.2) * ψ j).re := by
  simp only [sum_sum_re_star_mul_kronecker_mul]
  exact (hA.kronecker hB).isDistribution_re_star_dotProduct (star_dotProduct_self_eq_one hψ)

end Complex

section PartialTrace

variable {R : Type*} [AddCommMonoid R]

/-- The partial trace over the right factor: `(traceRight X) i j = ∑ k, X (i, k) (j, k)`. -/
def traceRight [Fintype n] (X : Matrix (m × n) (m × n) R) : Matrix m m R :=
  fun i j => ∑ k, X (i, k) (j, k)

/-- The partial trace over the left factor: `(traceLeft X) i j = ∑ k, X (k, i) (k, j)`. -/
def traceLeft [Fintype m] (X : Matrix (m × n) (m × n) R) : Matrix n n R :=
  fun i j => ∑ k, X (k, i) (k, j)

lemma traceRight_apply [Fintype n] (X : Matrix (m × n) (m × n) R) (i j : m) :
    traceRight X i j = ∑ k, X (i, k) (j, k) := rfl

lemma traceLeft_apply [Fintype m] (X : Matrix (m × n) (m × n) R) (i j : n) :
    traceLeft X i j = ∑ k, X (k, i) (k, j) := rfl

variable [Fintype m] [Fintype n]

theorem trace_traceRight (X : Matrix (m × n) (m × n) R) : trace (traceRight X) = trace X := by
  simp only [Matrix.trace, Matrix.diag, traceRight, Fintype.sum_prod_type]

theorem trace_traceLeft (X : Matrix (m × n) (m × n) R) : trace (traceLeft X) = trace X := by
  simp only [Matrix.trace, Matrix.diag, traceLeft, Fintype.sum_prod_type]
  exact Finset.sum_comm

end PartialTrace

section PartialTraceRing

variable {R : Type*} [CommSemiring R] [Fintype m] [Fintype n]

omit [Fintype m] in
theorem traceRight_kronecker (A : Matrix m m R) (B : Matrix n n R) :
    traceRight (A ⊗ₖ B) = trace B • A := by
  ext i j
  simp [traceRight, Matrix.trace, ← Finset.mul_sum, mul_comm]

omit [Fintype n] in
theorem traceLeft_kronecker (A : Matrix m m R) (B : Matrix n n R) :
    traceLeft (A ⊗ₖ B) = trace A • B := by
  ext i j
  simp [traceLeft, Matrix.trace, ← Finset.sum_mul]

/-- Duality: measuring `A` on the reduced state is measuring `A ⊗ 1` on the joint state. -/
theorem trace_mul_traceRight [DecidableEq n] (A : Matrix m m R) (X : Matrix (m × n) (m × n) R) :
    trace (A * traceRight X) = trace ((A ⊗ₖ (1 : Matrix n n R)) * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceRight, Fintype.sum_prod_type,
    kronecker_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem trace_mul_traceLeft [DecidableEq m] (B : Matrix n n R) (X : Matrix (m × n) (m × n) R) :
    trace (B * traceLeft X) = trace (((1 : Matrix m m R) ⊗ₖ B) * X) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, traceLeft, Fintype.sum_prod_type,
    kronecker_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.mul_sum]
  conv_rhs => enter [2, x, 2, y]; rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc ∑ i, ∑ j, ∑ k, B i j * X (k, j) (k, i) = ∑ i, ∑ k, ∑ j, B i j * X (k, j) (k, i) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, B i j * X (k, j) (k, i) := Finset.sum_comm

/-- No-signalling: summing a product measurement over the outcomes of the right party leaves the
measurement of the left party on the reduced state. -/
theorem sum_trace_kronecker_mul [DecidableEq n] [Fintype κ] (A : Matrix m m R) {F : κ → Matrix n n R}
    (hF : ∑ b, F b = 1) (X : Matrix (m × n) (m × n) R) :
    ∑ b, trace ((A ⊗ₖ F b) * X) = trace (A * traceRight X) := by
  rw [trace_mul_traceRight, ← hF, kronecker_sum, Finset.sum_mul, trace_sum]

theorem sum_trace_kronecker_mul_left [DecidableEq m] [Fintype ι] {E : ι → Matrix m m R}
    (hE : ∑ a, E a = 1) (B : Matrix n n R) (X : Matrix (m × n) (m × n) R) :
    ∑ a, trace ((E a ⊗ₖ B) * X) = trace (B * traceLeft X) := by
  rw [trace_mul_traceLeft, ← hE, sum_kronecker, Finset.sum_mul, trace_sum]

end PartialTraceRing

section PartialTracePositive

variable {𝕜 : Type*} [RCLike 𝕜] [Fintype m] [Fintype n]

omit [Fintype m] in
theorem posSemidef_traceRight {X : Matrix (m × n) (m × n) 𝕜} (hX : X.PosSemidef) :
    (traceRight X).PosSemidef := by
  have : traceRight X = ∑ k, X.submatrix (fun i => (i, k)) (fun i => (i, k)) := by
    ext i j
    simp [traceRight, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun k _ => hX.submatrix _

omit [Fintype n] in
theorem posSemidef_traceLeft {X : Matrix (m × n) (m × n) 𝕜} (hX : X.PosSemidef) :
    (traceLeft X).PosSemidef := by
  have : traceLeft X = ∑ k, X.submatrix (fun i => (k, i)) (fun i => (k, i)) := by
    ext i j
    simp [traceLeft, Matrix.sum_apply]
  rw [this]
  exact posSemidef_sum _ fun k _ => hX.submatrix _

/-- The reduced state of a density matrix is a density matrix. -/
theorem isDensity_traceRight {X : Matrix (m × n) (m × n) 𝕜} (hX : IsDensity X) :
    IsDensity (traceRight X) :=
  ⟨posSemidef_traceRight hX.1, by rw [trace_traceRight, hX.2]⟩

theorem isDensity_traceLeft {X : Matrix (m × n) (m × n) 𝕜} (hX : IsDensity X) :
    IsDensity (traceLeft X) :=
  ⟨posSemidef_traceLeft hX.1, by rw [trace_traceLeft, hX.2]⟩

end PartialTracePositive

section Unitary

variable [Fintype m] [Fintype n]

/-- An isometry `Vᴴ V = 1` preserves `∑ normSq`. -/
theorem sum_normSq_mulVec_of_isometry [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1)
    (ψ : n → ℂ) : ∑ i, Complex.normSq ((V *ᵥ ψ) i) = ∑ i, Complex.normSq (ψ i) := by
  apply Complex.ofReal_injective
  rw [ofReal_sum_normSq, ofReal_sum_normSq, star_mulVec, dotProduct_mulVec, vecMul_vecMul, hV,
    vecMul_one]

theorem sum_normSq_mulVec_of_mem_unitaryGroup [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (ψ : n → ℂ) :
    ∑ i, Complex.normSq ((U *ᵥ ψ) i) = ∑ i, Complex.normSq (ψ i) :=
  sum_normSq_mulVec_of_isometry (V := U) (Matrix.mem_unitaryGroup_iff'.mp hU) ψ

omit [Fintype n] in
/-- Each column of an isometry has unit length. -/
theorem sum_normSq_col_of_isometry [DecidableEq n] {V : Matrix m n ℂ} (hV : Vᴴ * V = 1) (j : n) :
    ∑ i, Complex.normSq (V i j) = 1 := by
  apply Complex.ofReal_injective
  have := congrFun (congrFun hV j) j
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  simpa [Complex.normSq_eq_conj_mul_self] using this

theorem sum_normSq_col_of_mem_unitaryGroup [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (j : n) : ∑ i, Complex.normSq (U i j) = 1 :=
  sum_normSq_col_of_isometry (V := U) (Matrix.mem_unitaryGroup_iff'.mp hU) j

theorem sum_normSq_row_of_mem_unitaryGroup [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (i : n) : ∑ j, Complex.normSq (U i j) = 1 := by
  apply Complex.ofReal_injective
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hU) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
  simpa [Complex.mul_conj] using this

/-- Measuring the column `U *ᵥ e_j` of a unitary in the computational basis: the outcome
distribution `i ↦ normSq (U i j)`. -/
theorem isDistribution_normSq_col [DecidableEq n] {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (j : n) : IsDistribution fun i => Complex.normSq (U i j) :=
  ⟨fun _ => Complex.normSq_nonneg _, sum_normSq_col_of_mem_unitaryGroup hU j⟩

/-- The probability of an event in the outcome of a unit vector is at most one. -/
theorem sum_ite_normSq_le_one {ψ : n → ℂ} (hψ : ∑ i, Complex.normSq (ψ i) = 1) (P : n → Prop)
    [DecidablePred P] : ∑ i, (if P i then Complex.normSq (ψ i) else 0) ≤ 1 := by
  rw [← hψ]
  exact Finset.sum_le_sum fun i _ => by
    split_ifs
    · exact le_rfl
    · exact Complex.normSq_nonneg _

end Unitary

end

end TheoremOS.LinearAlgebra
