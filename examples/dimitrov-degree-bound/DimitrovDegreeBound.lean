import Submission

set_option warningAsError true

namespace TheoremOS.DimitrovReuse

variable {K : Type*} [Field K] [NumberField K]

/-- The Dimitrov lower bound with field degree in place of the number of arguments. -/
theorem house_lower_bound_from_degree (α : K) (hIntegral : IsIntegral ℤ α)
    (hNonzero : α ≠ 0) (hInfiniteOrder : ¬ IsOfFinOrder α) :
    (2 : ℝ) ^ (1 / (4 * (Module.finrank ℚ K : ℝ)) : ℝ) ≤ NumberField.house α := by
  classical
  let args := Finset.univ.image fun σ : K →+* ℂ ↦ (σ α).arg
  have hArgsPositive : 0 < args.card := Submission.Helpers.argument_card_pos α
  have hArgsCount : args.card ≤ Module.finrank ℚ K := by
    calc
      args.card ≤ (Finset.univ : Finset (K →+* ℂ)).card := Finset.card_image_le
      _ = Module.finrank ℚ K := by
        rw [Finset.card_univ, NumberField.Embeddings.card]
  have hDenominatorPositive : 0 < 4 * (args.card : ℝ) :=
    mul_pos (by norm_num) (by exact_mod_cast hArgsPositive)
  have hDenominatorLe : 4 * (args.card : ℝ) ≤ 4 * (Module.finrank ℚ K : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hArgsCount) (by norm_num)
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (one_div_le_one_div_of_le hDenominatorPositive hDenominatorLe)).trans
    (Submission.dimitrov α hIntegral hNonzero hInfiniteOrder)

/-- Bounds on every conjugate certify that a nonzero algebraic integer is a root of unity. -/
theorem pow_eq_one_of_conjugates_lt_degree_bound (α : K) (hIntegral : IsIntegral ℤ α)
    (hNonzero : α ≠ 0)
    (hConjugates : ∀ σ : K →+* ℂ, ‖σ α‖ < (2 : ℝ) ^ (1 / (4 * (Module.finrank ℚ K : ℝ)) : ℝ)) :
    ∃ n : ℕ, 0 < n ∧ α ^ n = 1 := by
  classical
  apply isOfFinOrder_iff_pow_eq_one.mp
  by_contra hInfiniteOrder
  have hHouse : NumberField.house α < (2 : ℝ) ^ (1 / (4 * (Module.finrank ℚ K : ℝ)) : ℝ) := by
    have hUniv : (Finset.univ : Finset (K →+* ℂ)).Nonempty := Finset.univ_nonempty
    obtain ⟨σ, -, hMaximum⟩ := Finset.exists_mem_eq_sup' hUniv (fun f ↦ ‖f α‖₊)
    rw [NumberField.house_eq_sup', hMaximum]
    exact hConjugates σ
  exact (not_lt_of_ge (house_lower_bound_from_degree α hIntegral hNonzero hInfiniteOrder)) hHouse

#print axioms house_lower_bound_from_degree
#print axioms pow_eq_one_of_conjugates_lt_degree_bound

end TheoremOS.DimitrovReuse
