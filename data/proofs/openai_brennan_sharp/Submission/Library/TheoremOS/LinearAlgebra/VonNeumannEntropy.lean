import Submission.Library.TheoremOS.LinearAlgebra.DensityMatrix

/-!
# Von Neumann entropy through the continuous functional calculus

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ` and any `f : ℝ → ℝ`, `tr (cfc f A)` is the sum of
`f` over the eigenvalues of `A` (`trace_cfc_eq_sum`). The von Neumann entropy
`vonNeumannEntropy ρ = re tr (cfc negMulLog ρ)` (the spectral `-tr (ρ log ρ)` with `0 log 0 = 0`)
is the Shannon entropy of the eigenvalues; the eigenvalues of a density matrix form a
distribution, so `0 ≤ S(ρ) ≤ log d`; `S` of a scalar matrix and of the maximally mixed state;
invariance of `S` under unitary conjugation; and the two-sided bound
`|S(∑ w a • ρ a) - ∑ w a S(ρ a)| ≤ log d` for the Holevo-type quantity of an ensemble.

Sources: M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
University Press, 2000, Section 11.3 (von Neumann entropy, Theorem 11.8) and Section 12.1.1
(Holevo χ quantity); M. M. Wilde, *Quantum Information Theory*, 2nd ed., Cambridge University
Press, 2017, Section 11.1. Textbook material; nothing here is specific to a benchmark problem.

Bridges: a definition `S P := (Matrix.trace (cfc Real.negMulLog P)).re` over `ℂ` is
`vonNeumannEntropy P` by `rfl` (`RCLike.re` is `Complex.re` there, `RCLike.re_to_complex`), and
`IsState P := P.PosSemidef ∧ trace P = 1` is `IsDensity P` by `Iff.rfl`. Weights given as fields
`weight_nonneg` and `weight_sum` form `IsDistribution weight` by `⟨weight_nonneg, weight_sum⟩`.
Mathlib has `Matrix.IsHermitian.cfc_eq`, `Matrix.IsHermitian.trace_eq_sum_eigenvalues`,
`Matrix.PosSemidef.eigenvalues_nonneg` and `cfc_algebraMap`.
-/

namespace TheoremOS.LinearAlgebra

open Finset Matrix Real
open scoped BigOperators ComplexOrder MatrixOrder
open TheoremOS.InformationTheory

variable {ι n : Type*} {𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- `tr (cfc f A) = ∑ i, f (λᵢ)` for Hermitian `A`. -/
theorem trace_cfc_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    trace (cfc f A) = ∑ i, (f (hA.eigenvalues i) : 𝕜) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, trace_diagonal]
  rfl

theorem re_trace_cfc_eq_sum {A : Matrix n n 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    RCLike.re (trace (cfc f A)) = ∑ i, f (hA.eigenvalues i) := by
  rw [trace_cfc_eq_sum hA, map_sum]
  simp only [RCLike.ofReal_re]

/-- The von Neumann entropy `S(ρ) = -tr (ρ log ρ)`, spectrally, with `0 log 0 = 0`. -/
noncomputable def vonNeumannEntropy (ρ : Matrix n n 𝕜) : ℝ :=
  RCLike.re (trace (cfc negMulLog ρ))

lemma vonNeumannEntropy_def (ρ : Matrix n n 𝕜) :
    vonNeumannEntropy ρ = RCLike.re (trace (cfc negMulLog ρ)) := rfl

/-- `S(A)` is the Shannon entropy of the eigenvalues of `A`. -/
theorem vonNeumannEntropy_eq_entropy {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    vonNeumannEntropy A = entropy hA.eigenvalues :=
  re_trace_cfc_eq_sum hA negMulLog

/-- `S(r • 1) = d · negMulLog r`. -/
theorem vonNeumannEntropy_algebraMap (r : ℝ) :
    vonNeumannEntropy (algebraMap ℝ (Matrix n n 𝕜) r) = Fintype.card n * negMulLog r := by
  rw [vonNeumannEntropy_def, cfc_algebraMap r negMulLog,
    algebraMap_eq_diagonal, trace_diagonal]
  simp [Pi.algebraMap_apply]

namespace IsDensity

variable {ρ : Matrix n n 𝕜}

/-- The eigenvalues of a density matrix form a probability distribution. -/
theorem isDistribution_eigenvalues (h : IsDensity ρ) :
    IsDistribution h.isHermitian.eigenvalues where
  nonneg := h.posSemidef.eigenvalues_nonneg
  sum_eq_one := by
    have := h.isHermitian.trace_eq_sum_eigenvalues
    rw [h.trace_eq_one] at this
    exact_mod_cast this.symm

theorem vonNeumannEntropy_eq_entropy (h : IsDensity ρ) :
    vonNeumannEntropy ρ = entropy h.isHermitian.eigenvalues :=
  TheoremOS.LinearAlgebra.vonNeumannEntropy_eq_entropy h.isHermitian

/-- `0 ≤ S(ρ)`. -/
theorem vonNeumannEntropy_nonneg (h : IsDensity ρ) : 0 ≤ vonNeumannEntropy ρ := by
  rw [h.vonNeumannEntropy_eq_entropy]
  exact entropy_nonneg h.isDistribution_eigenvalues

/-- `S(ρ) ≤ log d`. -/
theorem vonNeumannEntropy_le_log_card (h : IsDensity ρ) :
    vonNeumannEntropy ρ ≤ log (Fintype.card n) := by
  rw [h.vonNeumannEntropy_eq_entropy]
  exact entropy_le_log_card h.isDistribution_eigenvalues

omit [DecidableEq n] in
theorem nonempty (h : IsDensity ρ) : Nonempty n := h.isDistribution_diag.nonempty

end IsDensity

section MaximallyMixed

/-- The maximally mixed state `1 / d`. -/
noncomputable def maximallyMixed (n 𝕜 : Type*) [RCLike 𝕜] [Fintype n] [DecidableEq n] :
    Matrix n n 𝕜 :=
  algebraMap ℝ (Matrix n n 𝕜) (Fintype.card n : ℝ)⁻¹

theorem isDensity_maximallyMixed [Nonempty n] : IsDensity (maximallyMixed n 𝕜) := by
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨?_, ?_⟩
  · rw [maximallyMixed, algebraMap_eq_diagonal, posSemidef_diagonal_iff]
    intro i
    simp only [Pi.algebraMap_apply, RCLike.algebraMap_eq_ofReal]
    exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (Nat.cast_nonneg _))
  · rw [maximallyMixed, algebraMap_eq_diagonal, trace_diagonal]
    simp only [Pi.algebraMap_apply, RCLike.algebraMap_eq_ofReal, sum_const, card_univ,
      nsmul_eq_mul]
    rw [← RCLike.ofReal_natCast, ← RCLike.ofReal_mul, mul_inv_cancel₀ hc, RCLike.ofReal_one]

/-- `S(1 / d) = log d`. -/
theorem vonNeumannEntropy_maximallyMixed [Nonempty n] :
    vonNeumannEntropy (maximallyMixed n 𝕜) = log (Fintype.card n) := by
  have hc : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [maximallyMixed, vonNeumannEntropy_algebraMap, negMulLog, log_inv]
  field_simp

end MaximallyMixed

/-- `S(U A U⋆) = S(A)` for a unitary `U` and Hermitian `A`. -/
theorem vonNeumannEntropy_unitary_conj {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (U : unitary (Matrix n n 𝕜)) :
    vonNeumannEntropy ((U : Matrix n n 𝕜) * A * star (U : Matrix n n 𝕜)) =
      vonNeumannEntropy A := by
  have hcont : Continuous (Unitary.conjStarAlgAut ℝ (Matrix n n 𝕜) U) := by
    have : ⇑(Unitary.conjStarAlgAut ℝ (Matrix n n 𝕜) U) =
        fun x => (U : Matrix n n 𝕜) * x * star (U : Matrix n n 𝕜) :=
      funext fun x => Unitary.conjStarAlgAut_apply U x
    rw [this]
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hsa : IsSelfAdjoint A := hA.isSelfAdjoint
  have hsa' : IsSelfAdjoint ((U : Matrix n n 𝕜) * A * star (U : Matrix n n 𝕜)) :=
    hsa.conjugate _
  have key := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℝ (Matrix n n 𝕜) U) negMulLog A
    (hf := continuous_negMulLog.continuousOn) (hφ := hcont) (ha := hsa)
    (hφa := by rw [Unitary.conjStarAlgAut_apply]; exact hsa')
  rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply] at key
  rw [vonNeumannEntropy_def, vonNeumannEntropy_def, ← key, trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

section Ensemble

variable [Fintype ι] {w : ι → ℝ} {ρ : ι → Matrix n n 𝕜}

/-- The Holevo-type quantity `S(∑ w a • ρ a) - ∑ w a S(ρ a)` of an ensemble is at most `log d`. -/
theorem vonNeumannEntropy_sum_smul_sub_le (hw : IsDistribution w) (hρ : ∀ a, IsDensity (ρ a)) :
    vonNeumannEntropy (∑ a, (w a : 𝕜) • ρ a) - ∑ a, w a * vonNeumannEntropy (ρ a) ≤
      log (Fintype.card n) := by
  have h1 := (IsDensity.sum_smul hw hρ).vonNeumannEntropy_le_log_card
  have h2 : 0 ≤ ∑ a, w a * vonNeumannEntropy (ρ a) :=
    sum_nonneg fun a _ => mul_nonneg (hw.nonneg a) (hρ a).vonNeumannEntropy_nonneg
  linarith

/-- `-log d ≤ S(∑ w a • ρ a) - ∑ w a S(ρ a)`. -/
theorem neg_log_card_le_vonNeumannEntropy_sum_smul_sub (hw : IsDistribution w)
    (hρ : ∀ a, IsDensity (ρ a)) :
    -log (Fintype.card n) ≤
      vonNeumannEntropy (∑ a, (w a : 𝕜) • ρ a) - ∑ a, w a * vonNeumannEntropy (ρ a) := by
  have h1 := (IsDensity.sum_smul hw hρ).vonNeumannEntropy_nonneg
  have h2 : ∑ a, w a * vonNeumannEntropy (ρ a) ≤ ∑ a, w a * log (Fintype.card n) :=
    sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (hρ a).vonNeumannEntropy_le_log_card (hw.nonneg a)
  rw [← sum_mul, hw.sum_eq_one, one_mul] at h2
  linarith

theorem abs_vonNeumannEntropy_sum_smul_sub_le (hw : IsDistribution w)
    (hρ : ∀ a, IsDensity (ρ a)) :
    |vonNeumannEntropy (∑ a, (w a : 𝕜) • ρ a) - ∑ a, w a * vonNeumannEntropy (ρ a)| ≤
      log (Fintype.card n) :=
  abs_le.mpr ⟨neg_log_card_le_vonNeumannEntropy_sum_smul_sub hw hρ,
    vonNeumannEntropy_sum_smul_sub_le hw hρ⟩

end Ensemble

end TheoremOS.LinearAlgebra
