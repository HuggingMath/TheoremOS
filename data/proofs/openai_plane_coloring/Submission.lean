import Mathlib

namespace OAI

noncomputable section

namespace Problem160

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def ProperColoring (k : ℕ) : Prop :=
  ∃ c : Plane → Fin k,
    ∀ x y : Plane, dist x y = 1 → c x ≠ c y

def triPoint (a b : ℤ) : Plane :=
  !₂[((3 : ℝ) / 4) * (a : ℝ) + ((3 : ℝ) / 8) * (b : ℝ),
    ((3 * Real.sqrt 3) / 8) * (b : ℝ)]
lemma triPoint_fst (a b : ℤ) :
    triPoint a b 0 = ((3 : ℝ) / 4) * (a : ℝ) + ((3 : ℝ) / 8) * (b : ℝ) := rfl
lemma triPoint_snd (a b : ℤ) :
    triPoint a b 1 = ((3 * Real.sqrt 3) / 8) * (b : ℝ) := rfl
noncomputable def colorOf (a b : ℤ) : Fin 7 :=
  (ZMod.finEquiv 7).symm ((a - 2 * b : ℤ) : ZMod 7)
lemma colorOf_sanity (a b c d : ℤ) :
    colorOf a b = colorOf c d ↔ (7 : ℤ) ∣ (a - 2 * b) - (c - 2 * d) := by
  unfold colorOf
  rw [((ZMod.finEquiv 7).symm.injective).eq_iff, ZMod.intCast_eq_intCast_iff_dvd_sub]
  rw [show (c - 2 * d) - (a - 2 * b) = -((a - 2 * b) - (c - 2 * d)) by ring, Int.dvd_neg]
  norm_num
theorem triPoint_sanity : ∀ a b : ℤ,
    dist (triPoint a b) (triPoint 0 0) ^ 2 =
      (3 / 4 : ℝ) ^ 2 * ((a : ℝ) ^ 2 + (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2) := by
  intro a b
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, triPoint]
  simp [mul_pow]
  ring_nf
  have h3 : |Real.sqrt 3| ^ 2 = 3 := by
    rw [sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [h3]
  ring
lemma sq_add_mul_add_sq_pos {p q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    0 < p ^ 2 + p * q + q ^ 2 := by
  have hnonneg : 0 ≤ p ^ 2 + p * q + q ^ 2 := by
    nlinarith [sq_nonneg (2 * p + q), sq_nonneg q]
  rcases eq_or_lt_of_le hnonneg with h0 | hpos
  · exfalso
    have hq2 : q ^ 2 = 0 := by
      nlinarith [sq_nonneg (2 * p + q), sq_nonneg q, h0]
    have hq0 : q = 0 := sq_eq_zero_iff.mp hq2
    have hp2 : p ^ 2 = 0 := by
      rw [hq0] at h0
      simpa using h0.symm
    have hp0 : p = 0 := sq_eq_zero_iff.mp hp2
    exact h.elim (fun hp => hp hp0) (fun hq => hq hq0)
  · exact hpos
theorem sameColor_norm : ∀ a b c d : ℤ,
    colorOf a b = colorOf c d → (a, b) ≠ (c, d) →
      (7 : ℤ) ≤ (a - c) ^ 2 + (a - c) * (b - d) + (b - d) ^ 2 := by
  intro a b c d h hne
  -- Same color means `7 ∣ (a - 2b) - (c - 2d)`, i.e. `7 ∣ (a-c) - 2(b-d)`.
  have hdvd : (7 : ℤ) ∣ (a - c) - 2 * (b - d) := by
    have h' := (colorOf_sanity a b c d).1 h
    rwa [show (a - 2 * b) - (c - 2 * d) = (a - c) - 2 * (b - d) by ring] at h'
  obtain ⟨k, hk⟩ := hdvd
  set p := a - c with hp
  set q := b - d with hq
  -- Distinct lattice coordinates give a nonzero difference vector.
  have hpq : p ≠ 0 ∨ q ≠ 0 := by
    rcases eq_or_ne p 0 with hp0 | hp0
    · right
      intro hq0
      have ha : a = c := by linarith
      have hb : b = d := by linarith
      exact hne (by rw [ha, hb])
    · exact Or.inl hp0
  -- Substituting `p = 2q + 7k` shows `7` divides the Eisenstein norm.
  have hp' : p = 2 * q + 7 * k := by linarith
  have hdvdN : (7 : ℤ) ∣ p ^ 2 + p * q + q ^ 2 :=
    ⟨q ^ 2 + 5 * q * k + 7 * k ^ 2, by rw [hp']; ring⟩
  exact Int.le_of_dvd (sq_add_mul_add_sq_pos hpq) hdvdN
theorem lattice_norm : ∀ a b c d : ℤ,
    dist (triPoint a b) (triPoint c d) ^ 2 =
      (3 / 4 : ℝ) ^ 2 *
        (((a - c : ℤ) : ℝ) ^ 2 + ((a - c : ℤ) : ℝ) * ((b - d : ℤ) : ℝ) +
          ((b - d : ℤ) : ℝ) ^ 2) := by
  intro a b c d
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, triPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [Real.dist_eq, sq_abs]
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  ring
theorem sameColor_dist_large (a b c d : ℤ)
    (h : colorOf a b = colorOf c d) (hne : (a, b) ≠ (c, d)) :
    1 + 2 * (3 / (4 * Real.sqrt 3)) <
      dist (triPoint a b) (triPoint c d) := by
  set x : ℤ := a - c
  set y : ℤ := b - d
  have hQint : (7 : ℤ) ≤ x ^ 2 + x * y + y ^ 2 := by
    simpa [x, y] using sameColor_norm a b c d h hne
  have hQreal : (7 : ℝ) ≤ (x : ℝ) ^ 2 + (x : ℝ) * (y : ℝ) + (y : ℝ) ^ 2 := by
    exact_mod_cast hQint
  have hln := lattice_norm a b c d
  have hd_sq : dist (triPoint a b) (triPoint c d) ^ 2 =
      (3 / 4 : ℝ) ^ 2 * ((x : ℝ) ^ 2 + (x : ℝ) * (y : ℝ) + (y : ℝ) ^ 2) := by
    simpa [x, y] using hln
  have hd_sq_ge : (63 / 16 : ℝ) ≤ dist (triPoint a b) (triPoint c d) ^ 2 := by
    rw [hd_sq]
    nlinarith
  let r : ℝ := 3 / (4 * Real.sqrt 3)
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hr_lt_half : r < 1 / 2 := by
    dsimp [r]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sqrt 3)]
    nlinarith
  have hr_sq : r ^ 2 = (3 / 16 : ℝ) := by
    dsimp [r]
    field_simp
    nlinarith
  let bnd : ℝ := 1 + 2 * r
  have hbnd_sq_lt : bnd ^ 2 < (63 / 16 : ℝ) := by
    dsimp [bnd]
    nlinarith
  have hbnd_nonneg : 0 ≤ bnd := by
    dsimp [bnd]
    positivity
  have hdist_nonneg : 0 ≤ dist (triPoint a b) (triPoint c d) := dist_nonneg
  have hsq : bnd ^ 2 < dist (triPoint a b) (triPoint c d) ^ 2 := by
    nlinarith
  have habs : |bnd| < |dist (triPoint a b) (triPoint c d)| := (sq_lt_sq.mp hsq)
  have : bnd < dist (triPoint a b) (triPoint c d) := by
    simpa [abs_of_nonneg hbnd_nonneg, abs_of_nonneg hdist_nonneg] using habs
  simpa [bnd, r] using this
def planeEis (u v : ℝ) : ℝ := u ^ 2 + u * v + v ^ 2
lemma planeEis_corner00 {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : 2 * p + q ≤ 1)
    (ht : p + 2 * q ≤ 1) : planeEis p q ≤ 1 / 3 := by
  unfold planeEis
  nlinarith [sq_nonneg (2 * p + q), sq_nonneg (p + 2 * q), mul_nonneg hp hq,
    mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr ht)]
lemma planeEis_corner10 {p q : ℝ} (hp : p ≤ 1) (hq : 0 ≤ q) (hpq : q ≤ p) (hs : 1 ≤ 2 * p + q)
    (ht : p + 2 * q ≤ 2) : planeEis (p - 1) q ≤ 1 / 3 := by
  unfold planeEis
  nlinarith [sq_nonneg (1 - p - 2 * q), sq_nonneg (2 * p + q - 1), sq_nonneg (1 - p - q),
    mul_nonneg (sub_nonneg.mpr hp) hq]
lemma planeEis_corner01 {p q : ℝ} (hp0 : 0 ≤ p) (hq : q ≤ 1) (hpq : p ≤ q) (hs : 1 ≤ p + 2 * q)
    (ht : 2 * p + q ≤ 2) : planeEis p (q - 1) ≤ 1 / 3 := by
  have h := planeEis_corner10 hq hp0 hpq (by linarith : 1 ≤ 2 * q + p) (by linarith : q + 2 * p ≤ 2)
  unfold planeEis at *
  nlinarith [h]
lemma planeEis_corner11 {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) (hs : 2 ≤ 2 * p + q)
    (ht : 2 ≤ p + 2 * q) : planeEis (p - 1) (q - 1) ≤ 1 / 3 := by
  have a1 : 0 ≤ 1 - p := by linarith
  have b1 : 0 ≤ 1 - q := by linarith
  have e1 : 2 * (1 - p) + (1 - q) ≤ 1 := by linarith
  have e2 : (1 - p) + 2 * (1 - q) ≤ 1 := by linarith
  have h := planeEis_corner00 a1 b1 e1 e2
  unfold planeEis at *
  nlinarith [h]
lemma planeEis_corners {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    planeEis p q ≤ 1 / 3 ∨ planeEis (p - 1) q ≤ 1 / 3 ∨ planeEis p (q - 1) ≤ 1 / 3 ∨
      planeEis (p - 1) (q - 1) ≤ 1 / 3 := by
  by_cases hA : 2 * p + q ≤ 1 ∧ p + 2 * q ≤ 1
  · exact Or.inl (planeEis_corner00 hp0 hq0 hA.1 hA.2)
  by_cases hD : 2 ≤ 2 * p + q ∧ 2 ≤ p + 2 * q
  · exact Or.inr (Or.inr (Or.inr (planeEis_corner11 hp1 hq1 hD.1 hD.2)))
  rcases le_total q p with hqp | hpq
  · have h1 : 1 ≤ 2 * p + q := by
      rcases le_or_gt (2 * p + q) 1 with h | h
      · have h2 : 1 < p + 2 * q := by
          rcases le_or_gt (p + 2 * q) 1 with h2 | h2
          · exact absurd ⟨h, h2⟩ hA
          · exact h2
        linarith
      · exact h.le
    have h2 : p + 2 * q ≤ 2 := by
      rcases le_or_gt (p + 2 * q) 2 with h | h
      · exact h
      · exact absurd ⟨by linarith, by linarith⟩ hD
    exact Or.inr (Or.inl (planeEis_corner10 hp1 hq0 hqp h1 h2))
  · have h1 : 1 ≤ p + 2 * q := by
      rcases le_or_gt (p + 2 * q) 1 with h | h
      · have h2 : 1 < 2 * p + q := by
          rcases le_or_gt (2 * p + q) 1 with h2 | h2
          · exact absurd ⟨h2, h⟩ hA
          · exact h2
        linarith
      · exact h.le
    have h2 : 2 * p + q ≤ 2 := by
      rcases le_or_gt (2 * p + q) 2 with h | h
      · exact h
      · exact absurd ⟨by linarith, by linarith⟩ hD
    exact Or.inr (Or.inr (Or.inl (planeEis_corner01 hp0 hq1 hpq h1 h2)))
theorem covering : ∀ x : Plane, ∃ a b : ℤ,
    dist x (triPoint a b) ≤ 3 / (4 * Real.sqrt 3) := by
  intro x
  have h3 : Real.sqrt 3 ^ 2 = (3 : ℝ) := by
    rw [sq, Real.mul_self_sqrt (by norm_num)]
  set X : ℝ := x 0 with hX
  set Y : ℝ := x 1 with hY
  set α : ℝ := 4 * X / 3 - 4 * Y / (3 * Real.sqrt 3) with hαdef
  set β : ℝ := 8 * Y / (3 * Real.sqrt 3) with hβdef
  set p : ℝ := Int.fract α with hpdef
  set q : ℝ := Int.fract β with hqdef
  have hp0 : 0 ≤ p := Int.fract_nonneg α
  have hp1 : p < 1 := Int.fract_lt_one α
  have hq0 : 0 ≤ q := Int.fract_nonneg β
  have hq1 : q < 1 := Int.fract_lt_one β
  have hα : ((⌊α⌋ : ℤ) : ℝ) + p = α := Int.floor_add_fract α
  have hβ : ((⌊β⌋ : ℤ) : ℝ) + q = β := Int.floor_add_fract β
  have hX' : X = (3 / 4) * α + (3 / 8) * β := by
    rw [hαdef, hβdef]
    field_simp
    ring
  have hY' : Y = (3 * Real.sqrt 3 / 8) * β := by
    rw [hβdef]
    field_simp
  have hformula : ∀ (m n : ℤ) (u v : ℝ), u = α - m → v = β - n →
      dist x (triPoint m n) ^ 2 = (9 / 16) * planeEis u v := by
    intro m n u v hu hv
    have hd : dist x (triPoint m n) ^ 2 =
        (x 0 - triPoint m n 0) ^ 2 + (x 1 - triPoint m n 1) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    rw [hd, triPoint_fst, triPoint_snd, ← hX, ← hY, hX', hY', hu, hv]
    unfold planeEis
    nlinarith [h3]
  have hr : (3 / (4 * Real.sqrt 3)) ^ 2 = (3 : ℝ) / 16 := by
    rw [div_pow, mul_pow, h3]
    norm_num
  have hfinish : ∀ (m n : ℤ) (u v : ℝ), u = α - m → v = β - n → planeEis u v ≤ 1 / 3 →
      dist x (triPoint m n) ≤ 3 / (4 * Real.sqrt 3) := by
    intro m n u v hu hv hle
    have hd := hformula m n u v hu hv
    have hr0 : 0 ≤ 3 / (4 * Real.sqrt 3) := by positivity
    nlinarith [hd, hle, hr, hr0, dist_nonneg (x := x) (y := triPoint m n)]
  rcases planeEis_corners hp0 hp1.le hq0 hq1.le with h | h | h | h
  · refine ⟨⌊α⌋, ⌊β⌋, hfinish ⌊α⌋ ⌊β⌋ p q ?_ ?_ h⟩
    · linarith
    · linarith
  · refine ⟨⌊α⌋ + 1, ⌊β⌋, hfinish (⌊α⌋ + 1) ⌊β⌋ (p - 1) q ?_ ?_ h⟩
    · push_cast; linarith
    · linarith
  · refine ⟨⌊α⌋, ⌊β⌋ + 1, hfinish ⌊α⌋ (⌊β⌋ + 1) p (q - 1) ?_ ?_ h⟩
    · linarith
    · push_cast; linarith
  · refine ⟨⌊α⌋ + 1, ⌊β⌋ + 1, hfinish (⌊α⌋ + 1) (⌊β⌋ + 1) (p - 1) (q - 1) ?_ ?_ h⟩
    · push_cast; linarith
    · push_cast; linarith
noncomputable def triColor (x : Plane) : Fin 7 :=
  colorOf (Classical.choose (covering x))
    (Classical.choose (Classical.choose_spec (covering x)))
theorem triColor_sanity (x : Plane) : ∃ a b : ℤ,
    dist x (triPoint a b) ≤ 3 / (4 * Real.sqrt 3) ∧
      triColor x = colorOf a b := by
  let a : ℤ := Classical.choose (covering x)
  let h : ∃ b : ℤ, dist x (triPoint a b) ≤ 3 / (4 * Real.sqrt 3) :=
    Classical.choose_spec (covering x)
  let b : ℤ := Classical.choose h
  refine ⟨a, b, Classical.choose_spec h, ?_⟩
  dsimp only [triColor, a, b, h]
lemma covering_radius_lt_half : (3 : ℝ) / (4 * Real.sqrt 3) < 1 / 2 := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * Real.sqrt 3)]
  have hsq : (3 : ℝ) ^ 2 < (2 * Real.sqrt 3) ^ 2 := by nlinarith
  have habs : |(3 : ℝ)| < |2 * Real.sqrt 3| := sq_lt_sq.mp hsq
  have h2s : (0 : ℝ) ≤ 2 * Real.sqrt 3 := by positivity
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg h2s] at habs
  linarith
theorem proper_coloring : ∀ x y : Plane, dist x y = 1 → triColor x ≠ triColor y := by
  intro x y hxy hcol
  obtain ⟨a, b, hx, hcx⟩ := triColor_sanity x
  obtain ⟨c, d, hy, hcy⟩ := triColor_sanity y
  have hcolor : colorOf a b = colorOf c d := by rw [← hcx, hcol, hcy]
  by_cases hEq : (a, b) = (c, d)
  · have hac : a = c := by simpa using congrArg Prod.fst hEq
    have hbd : b = d := by simpa using congrArg Prod.snd hEq
    subst c
    subst d
    have htri : dist x y ≤ dist x (triPoint a b) + dist (triPoint a b) y :=
      dist_triangle x (triPoint a b) y
    have hcomm : dist (triPoint a b) y = dist y (triPoint a b) := dist_comm _ _
    have hlt : dist x y < 1 := by
      rw [hcomm] at htri
      nlinarith [htri, hx, hy, covering_radius_lt_half]
    linarith
  · have hlarge := sameColor_dist_large a b c d hcolor hEq
    have h1 : dist (triPoint a b) x ≤ 3 / (4 * Real.sqrt 3) := by
      simpa [dist_comm] using hx
    have h2 : dist x (triPoint c d) ≤ dist x y + dist y (triPoint c d) :=
      dist_triangle x y (triPoint c d)
    have h3 : dist (triPoint a b) (triPoint c d) ≤
        dist (triPoint a b) x + dist x (triPoint c d) :=
      dist_triangle (triPoint a b) x (triPoint c d)
    rw [hxy] at h2
    linarith
theorem properColoring_seven : ProperColoring 7 :=
  ⟨triColor, proper_coloring⟩
end Problem160

end

end OAI
