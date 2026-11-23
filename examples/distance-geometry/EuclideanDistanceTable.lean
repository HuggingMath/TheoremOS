import ArchivedEquiangularHelpers

namespace TheoremOS.DistanceGeometry

/-- The inner product table obtained by placing the anchor at the origin. -/
noncomputable def anchoredGram {n : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (anchor : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (D i anchor + D j anchor - D i j) / 2

/-- A table with zero diagonal gives squared distances in dimension `d` exactly when
its anchored Gram matrix is positive semidefinite and has rank at most `d`. -/
theorem squaredDistances_iff {n d : ℕ} (D : Matrix (Fin n) (Fin n) ℝ) (anchor : Fin n)
    (zeroDiagonal : ∀ i, D i i = 0) :
    (∃ points : Fin n → EuclideanSpace ℝ (Fin d), ∀ i j, dist (points i) (points j) ^ 2 = D i j) ↔
      (anchoredGram D anchor).PosSemidef ∧ (anchoredGram D anchor).rank ≤ d := by
  classical
  constructor
  · rintro ⟨points, distances⟩
    let shifted := fun i => points i - points anchor
    have normSq (i : Fin n) : ‖shifted i‖ ^ 2 = D i anchor := by
      simpa only [shifted, dist_eq_norm] using distances i anchor
    have distanceSq (i j : Fin n) : ‖shifted i - shifted j‖ ^ 2 = D i j := by
      have difference : shifted i - shifted j = points i - points j := by
        dsimp only [shifted]
        abel
      rw [difference, ← dist_eq_norm, distances]
    have gramEq : Matrix.gram ℝ shifted = anchoredGram D anchor := by
      ext i j
      rw [Matrix.gram_apply]
      change _ = (D i anchor + D j anchor - D i j) / 2
      have h := norm_sub_sq_real (shifted i) (shifted j)
      rw [distanceSq, normSq, normSq] at h
      linarith only [h]
    rw [← gramEq]
    refine ⟨Matrix.posSemidef_gram ℝ shifted, ?_⟩
    let basis := EuclideanSpace.basisFun (Fin d) ℝ
    let coordinates : Matrix (Fin d) (Fin n) ℝ := Matrix.of fun i j => basis.repr (shifted j) i
    rw [Matrix.gram_eq_conjTranspose_mul basis shifted]
    exact (Matrix.rank_mul_le_right coordinates.conjTranspose coordinates).trans
      (by simpa only [Fintype.card_fin] using Matrix.rank_le_card_height coordinates)
  · rintro ⟨positive, rankBound⟩
    obtain ⟨points, gramEq⟩ :=
      Submission.Helpers.positive_semidefinite_gram_realization n d _ positive rankBound
    have innerEq (i j : Fin n) :
        inner ℝ (points i) (points j) = (D i anchor + D j anchor - D i j) / 2 := by
      rw [← Matrix.gram_apply, gramEq]
      rfl
    have normSq (i : Fin n) : ‖points i‖ ^ 2 = D i anchor := by
      have h := innerEq i i
      rw [real_inner_self_eq_norm_sq, zeroDiagonal] at h
      linarith only [h]
    refine ⟨points, ?_⟩
    intro i j
    rw [dist_eq_norm, norm_sub_sq_real, normSq, normSq, innerEq]
    ring

def triangle345 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 9, 16; 9, 0, 25; 16, 25, 0]

/-- A 3–4–5 distance table can be realized exactly in dimensions two and above. -/
theorem triangle345_iff {d : ℕ} :
    (∃ points : Fin 3 → EuclideanSpace ℝ (Fin d),
      ∀ i j, dist (points i) (points j) ^ 2 = triangle345 i j) ↔ 2 ≤ d := by
  classical
  have zeroDiagonal (i : Fin 3) : triangle345 i i = 0 := by
    fin_cases i <;> norm_num [triangle345]
  rw [squaredDistances_iff triangle345 0 zeroDiagonal]
  have gramEq : anchoredGram triangle345 0 = Matrix.diagonal ![0, 9, 16] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [anchoredGram, triangle345, Matrix.diagonal_apply]
  rw [gramEq]
  have positive : (Matrix.diagonal (![0, 9, 16] : Fin 3 → ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  have rankEq : (Matrix.diagonal (![0, 9, 16] : Fin 3 → ℝ)).rank = 2 := by
    rw [Matrix.rank_diagonal, Fintype.card_subtype]
    have supportEq : (Finset.univ.filter fun i : Fin 3 => (![0, 9, 16] : Fin 3 → ℝ) i ≠ 0) =
        {1, 2} := by
      ext i
      fin_cases i <;> norm_num
    rw [supportEq]
    decide
  simp only [positive, rankEq, true_and]

#print axioms squaredDistances_iff
#print axioms triangle345_iff

end TheoremOS.DistanceGeometry
