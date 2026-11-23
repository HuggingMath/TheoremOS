import ArchivedHadamardCubeFiber

open OAI.HadamardSix
open scoped BigOperators Classical

namespace TheoremOS.SixPhaseCode

/-- Sixth roots of unity have two possible cubes. This word records which cube occurs. -/
noncomputable def binaryWord (H : Matrix6) (i k : Index) : Bool := decide (H i k ^ 3 = 1)

private lemma cube_eq_one_or_neg_one {z : ℂ} (hz : z ^ 6 = 1) :
    z ^ 3 = 1 ∨ z ^ 3 = -1 := by
  have h : (z ^ 3 - 1) * (z ^ 3 + 1) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

private lemma entry_mul_star {H : Matrix6} (hH : IsComplexHadamard H) (i k : Index) :
    H i k * star (H i k) = 1 := by
  rw [Complex.star_def, Complex.mul_conj', hH.1 i k]
  norm_num

private lemma ratio_pow_eq_one_iff {H : Matrix6} (hH : IsComplexHadamard H)
    (i j k : Index) (n : ℕ) :
    rowRatio H i j k ^ n = 1 ↔ H i k ^ n = H j k ^ n := by
  have h := congrArg (fun z : ℂ => z ^ n) (entry_mul_star hH j k)
  rw [mul_pow, one_pow] at h
  rw [rowRatio, mul_pow]
  constructor
  · intro he
    calc
      H i k ^ n = (H i k ^ n * star (H j k) ^ n) * H j k ^ n := by
        linear_combination -(H i k ^ n) * h
      _ = H j k ^ n := by rw [he, one_mul]
  · rintro he
    rw [he, h]

private lemma ratio_cube_class {H : Matrix6} (sixthRoot : ∀ i k, H i k ^ 6 = 1)
    (i j k : Index) : rowRatio H i j k ^ 3 = 1 ∨ rowRatio H i j k ^ 3 = -1 := by
  apply cube_eq_one_or_neg_one
  simp only [rowRatio, mul_pow, ← star_pow, sixthRoot, star_one, mul_one]

private lemma binaryWord_eq_iff {H : Matrix6} (sixthRoot : ∀ i k, H i k ^ 6 = 1)
    (i j k : Index) :
    binaryWord H i k = binaryWord H j k ↔ H i k ^ 3 = H j k ^ 3 := by
  rcases cube_eq_one_or_neg_one (sixthRoot i k) with hi | hi <;>
    rcases cube_eq_one_or_neg_one (sixthRoot j k) with hj | hj <;>
    norm_num [binaryWord, hi, hj]

/-- Within either binary class, the ternary projections agree at exactly a third
of the coordinates. Each binary class is specified by the cube of the row ratio. -/
theorem ternary_matches_in_binary_class {H : Matrix6} (hH : IsComplexHadamard H)
    (hSquare : IsComplexHadamard (entrywiseSquare H)) (sixthRoot : ∀ i k, H i k ^ 6 = 1)
    {i j : Index} (hne : i ≠ j) {sign : ℂ} (hSign : sign = 1 ∨ sign = -1) :
    let s := cubeFiber (rowRatio H i j) sign
    3 * (s.filter fun k => H i k ^ 2 = H j k ^ 2).card = s.card := by
  classical
  let r := rowRatio H i j
  let s := cubeFiber r sign
  change 3 * (s.filter fun k => H i k ^ 2 = H j k ^ 2).card = s.card
  have hfirst : ∑ k ∈ s, r k = 0 := by
    have hclass := ratio_cube_class sixthRoot i j
    rcases hSign with rfl | rfl
    · exact rowRatio_cubeFiber_sum_zero hH hSquare hne 1 (-1) (by norm_num) hclass
    · exact rowRatio_cubeFiber_sum_zero hH hSquare hne (-1) 1 (by norm_num)
        (fun k => (hclass k).symm)
  have hcube {k : Index} (hk : k ∈ s) : r k ^ 3 = sign := by
    simpa [s, cubeFiber] using hk
  have hUnit (k : Index) : r k * star (r k) = 1 := by
    dsimp only [r, rowRatio]
    rw [star_mul, star_star]
    calc
      H i k * star (H j k) * (H j k * star (H i k)) =
          (H i k * star (H i k)) * (H j k * star (H j k)) := by ring
      _ = 1 := by rw [entry_mul_star hH, entry_mul_star hH, mul_one]
  have hsecond : ∑ k ∈ s, r k ^ 2 = 0 := by
    calc
      _ = ∑ k ∈ s, sign * star (r k) := Finset.sum_congr rfl fun k hk => by
        rw [← hcube hk]
        linear_combination -(r k ^ 2) * hUnit k
      _ = 0 := by rw [← Finset.mul_sum, ← star_sum, hfirst, star_zero, mul_zero]
  have hfourth : ∑ k ∈ s, r k ^ 4 = 0 := by
    calc
      _ = ∑ k ∈ s, sign * r k := Finset.sum_congr rfl fun k hk => by
        rw [← hcube hk]
        ring
      _ = 0 := by rw [← Finset.mul_sum, hfirst, mul_zero]
  have hindicator (k : Index) :
      (if H i k ^ 2 = H j k ^ 2 then (3 : ℂ) else 0) = 1 + r k ^ 2 + r k ^ 4 := by
    simp only [← ratio_pow_eq_one_iff hH i j k 2]
    change (if r k ^ 2 = 1 then (3 : ℂ) else 0) = 1 + r k ^ 2 + r k ^ 4
    have hsix : r k ^ 6 = 1 := by
      simp only [r, rowRatio, mul_pow, ← star_pow, sixthRoot, star_one, mul_one]
    by_cases he : r k ^ 2 = 1
    · have hfour : r k ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, he, one_pow]
      norm_num [he, hfour]
    · rw [ite_eq_right he]
      have hfactor : (r k ^ 2 - 1) * (1 + r k ^ 2 + r k ^ 4) = 0 := by
        linear_combination hsix
      exact ((mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr he)).symm
  have hcount : (3 : ℂ) * ↑(s.filter fun k => H i k ^ 2 = H j k ^ 2).card = ↑s.card := by
    calc
      _ = ∑ k ∈ s, if H i k ^ 2 = H j k ^ 2 then (3 : ℂ) else 0 := by
        rw [← Finset.sum_filter]
        simp [mul_comm]
      _ = ∑ k ∈ s, (1 + r k ^ 2 + r k ^ 4) := Finset.sum_congr rfl fun k _ => hindicator k
      _ = _ := by simp [Finset.sum_add_distrib, hsecond, hfourth]
  exact_mod_cast hcount

/-- A pair of distinct rows projects to binary words at distance zero, three or six. -/
theorem binary_hamming_distance {H : Matrix6} (hH : IsComplexHadamard H)
    (hSquare : IsComplexHadamard (entrywiseSquare H)) (sixthRoot : ∀ i k, H i k ^ 6 = 1)
    {i j : Index} (hne : i ≠ j) :
    let d := hammingDist (binaryWord H i) (binaryWord H j)
    d = 0 ∨ d = 3 ∨ d = 6 := by
  classical
  have hEq : (Finset.univ.filter fun k => binaryWord H i k ≠ binaryWord H j k)
      = cubeFiber (rowRatio H i j) (-1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, cubeFiber]
    simp only [ne_eq, binaryWord_eq_iff sixthRoot, ← ratio_pow_eq_one_iff hH i j k 3]
    rcases ratio_cube_class sixthRoot i j k with h | h <;> norm_num [h]
  have hCount := ternary_matches_in_binary_class hH hSquare sixthRoot hne (Or.inr rfl :
    (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  dsimp only at hCount
  have hd : hammingDist (binaryWord H i) (binaryWord H j) ≤ Fintype.card Index :=
    hammingDist_le_card_fintype
  simp only [Fintype.card_fin] at hd
  have hCard : hammingDist (binaryWord H i) (binaryWord H j) =
      (cubeFiber (rowRatio H i j) (-1)).card := by
    rw [hammingDist, hEq]
  dsimp only
  omega

/-- At most one projected binary codeword lies within one error of a received word. -/
theorem unique_binary_correction {H : Matrix6} (hH : IsComplexHadamard H)
    (hSquare : IsComplexHadamard (entrywiseSquare H)) (sixthRoot : ∀ i k, H i k ^ 6 = 1)
    {i j : Index} {received : Index → Bool}
    (hi : hammingDist (binaryWord H i) received ≤ 1)
    (hj : hammingDist (binaryWord H j) received ≤ 1) : binaryWord H i = binaryWord H j := by
  by_cases hij : i = j
  · rw [hij]
  have htriangle := hammingDist_triangle_right (binaryWord H i) (binaryWord H j) received
  have hcases := binary_hamming_distance hH hSquare sixthRoot hij
  apply hammingDist_eq_zero.mp
  dsimp only at hcases
  omega

#print axioms ternary_matches_in_binary_class
#print axioms binary_hamming_distance
#print axioms unique_binary_correction

end TheoremOS.SixPhaseCode
