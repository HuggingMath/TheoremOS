import Mathlib

/-!
# Littlewood polynomials, aperiodic correlations and the merit factor

Finite trigonometric polynomials `trigPoly s c t = ∑_{k ∈ s} c k e_k(t)` on `AddCircle T` with
normalised Haar measure: the mean of a character (`integral_fourier_haarAddCircle`) and of a
trigonometric polynomial, Parseval `∫ |∑ c_k e_k|^2 = ∑ |c_k|^2` (`integral_norm_sq_trigPoly`),
integrability of continuous functions, and points where a continuous function is above or below
its mean. `e_1` parametrises the unit circle (`exists_fourier_one_eq`, `forall_norm_eq_one_iff`)
and `e_1(t)^k = e_k(t)` (`fourier_one_pow`).

Aperiodic autocorrelations `c_k = ∑_{j < N - k} a_j a_{j+k}` of a finite sequence over any
commutative ring (`aperiodicCorr`, through the zero extension `zeroExtend`), grouping a double sum
by the difference `j - l` (`sum_sum_mul_eq_sum_aperiodicCorr`), folding symmetric sums over
`(-N, N)` (`sum_Ioo_natAbs`) and `(∑ a_j)^2 = c_0 + 2 ∑_{k ≥ 1} c_k`.

Littlewood polynomials `P_a(z) = ∑_{k < N} a_k z^k` with real coefficients and `±1` sequences
(`IsSigning`): on the circle `|P_a|^2 = ∑_{|k| < N} c_{|k|} e_k`, so `∫ |P_a|^2 = ∑ a_k^2` and
`∫ |P_a|^4 = c_0^2 + 2 ∑_{k=1}^{N-1} c_k^2` (`integral_norm_pow_four_littlewoodPoly`). For a `±1`
sequence with off-peak energy `E = ∑_{k ≥ 1} c_k^2` and merit factor `F = N^2 / (2E)`:
`∫ (|P|^2/N - 1)^2 = 1/F`, `∫ (|P|/√N - 1)^2 ≤ 1/F` and, by Lyapunov's inequality on a probability
space (`integral_rpow_le_integral_rpow_rpow`), `∫ ||P|/√N - 1|^p ≤ F^(-p/2)` for `0 < p ≤ 2`.
Some point of the unit circle has `|P| ≥ √N` and another has `|P| ≤ √N`.

Sources: J. E. Littlewood, *Some Problems in Real and Complex Analysis*, Heath (1968);
P. Borwein, *Computational Excursions in Analysis and Number Theory*, Springer (2002);
M. J. E. Golay, *A class of finite binary sequences with alternate auto-correlation values equal
to zero*, IEEE Trans. Inform. Theory 18 (1972) 449–450 (merit factor); T. Høholdt and
H. E. Jensen, *Determination of the merit factor of Legendre sequences*, IEEE Trans. Inform.
Theory 34 (1988) 161–164 (the `L^4` identity); J. Jedwab, *A survey of the merit factor problem
for binary sequences*, SETA 2004, LNCS 3486 (2005) 30–55; Y. Katznelson, *An Introduction to
Harmonic Analysis*, ch. I (Parseval). Classical material; nothing here is specific to a benchmark
problem. There are no periodic correlations, circulant matrices, parity or mod-4 arguments, and no
constructions of flat or Rudin–Shapiro polynomials.

Bridges: a definition `∑ k : Fin N, (ε k : ℂ) * z ^ (k : ℕ)` is `littlewoodPoly ε z` by `rfl`,
`∀ k, ε k = -1 ∨ ε k = 1` is `IsSigning ε` by `Iff.rfl`, and
`∑ j : Fin (n - k), h ⟨j.val, _⟩ * h ⟨j.val + k, _⟩` is `aperiodicCorr h k`
(`aperiodicCorr_eq_sum_fin`). `UnitAddCircle` is `AddCircle 1`, `Real.rpow x p` is `x ^ p`, and
`(meritFactor a)⁻¹` is `2 * offPeakEnergy a / N ^ 2` (`inv_meritFactor`).
-/

namespace TheoremOS.Analysis

noncomputable section

open MeasureTheory AddCircle Finset
open scoped ComplexConjugate

section Circle

variable {T : ℝ}

/-- Continuous functions on the circle are integrable for normalised Haar measure. -/
theorem integrable_haarAddCircle_of_continuous [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    {f : AddCircle T → E} (hf : Continuous f) : Integrable f haarAddCircle :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The integral of a character: `∫ e_n = 1` if `n = 0` and `0` otherwise. -/
theorem integral_fourier_haarAddCircle [Fact (0 < T)] (n : ℤ) :
    ∫ t, fourier n t ∂(haarAddCircle (T := T)) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h
  rw [h, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem norm_fourier_apply (n : ℤ) (t : AddCircle T) : ‖fourier n t‖ = 1 := by
  simp [fourier_apply]

/-- Every point of the unit circle is `e_1 t` for some `t`. -/
theorem exists_fourier_one_eq [hT : Fact (0 < T)] {z : ℂ} (hz : ‖z‖ = 1) : ∃ t : AddCircle T, fourier 1 t = z := by
  have hT0 : T ≠ 0 := hT.out.ne'
  refine ⟨((T / (2 * Real.pi) * Complex.arg z : ℝ) : AddCircle T), ?_⟩
  rw [fourier_one, toCircle_apply_mk,
    show 2 * Real.pi / T * (T / (2 * Real.pi) * Complex.arg z) = Complex.arg z by
      field_simp, Circle.coe_exp]
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at this
  simpa using this

/-- Statements over the unit circle `‖z‖ = 1` are statements over `t ↦ e_1 t`. -/
theorem forall_norm_eq_one_iff [Fact (0 < T)] (P : ℂ → Prop) :
    (∀ z : ℂ, ‖z‖ = 1 → P z) ↔ ∀ t : AddCircle T, P (fourier 1 t) := by
  refine ⟨fun h t => h _ (norm_fourier_apply 1 t), fun h z hz => ?_⟩
  obtain ⟨t, rfl⟩ := exists_fourier_one_eq (T := T) hz
  exact h t

theorem fourier_one_pow (k : ℕ) (t : AddCircle T) : fourier 1 t ^ k = fourier (k : ℤ) t := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← fourier_add]; push_cast; rfl

/-- A continuous real function on the circle reaches its mean from above somewhere. -/
theorem exists_integral_le_apply [Fact (0 < T)] {g : AddCircle T → ℝ} (hg : Continuous g) :
    ∃ t, ∫ s, g s ∂haarAddCircle ≤ g t := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hg.continuousOn
  refine ⟨t, ?_⟩
  calc ∫ s, g s ∂haarAddCircle ≤ ∫ _s, g t ∂(haarAddCircle (T := T)) :=
        integral_mono (integrable_haarAddCircle_of_continuous hg)
          (integrable_const _) fun s => ht (Set.mem_univ s)
    _ = g t := by simp

/-- A continuous real function on the circle reaches its mean from below somewhere. -/
theorem exists_apply_le_integral [Fact (0 < T)] {g : AddCircle T → ℝ} (hg : Continuous g) :
    ∃ t, g t ≤ ∫ s, g s ∂haarAddCircle := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hg.continuousOn
  refine ⟨t, ?_⟩
  calc g t = ∫ _s, g t ∂(haarAddCircle (T := T)) := by simp
    _ ≤ ∫ s, g s ∂haarAddCircle :=
        integral_mono (integrable_const _) (integrable_haarAddCircle_of_continuous hg)
          fun s => ht (Set.mem_univ s)

end Circle

section TrigPoly

variable {T : ℝ}

/-- The trigonometric polynomial `t ↦ ∑_{k ∈ s} c k e_k(t)`. -/
def trigPoly (s : Finset ℤ) (c : ℤ → ℂ) (t : AddCircle T) : ℂ :=
  ∑ k ∈ s, c k * fourier k t

theorem continuous_trigPoly (s : Finset ℤ) (c : ℤ → ℂ) : Continuous (trigPoly (T := T) s c) := by
  unfold trigPoly
  fun_prop

/-- The mean of a trigonometric polynomial is its constant coefficient. -/
theorem integrable_trigPoly_term [Fact (0 < T)] (a : ℂ) (k : ℤ) :
    Integrable (fun t : AddCircle T => a * fourier k t) haarAddCircle :=
  integrable_haarAddCircle_of_continuous (continuous_const.mul (fourier k).continuous)

theorem integral_trigPoly [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    ∫ t, trigPoly s c t ∂(haarAddCircle (T := T)) = if 0 ∈ s then c 0 else 0 := by
  unfold trigPoly
  rw [integral_finsetSum s fun k _ => integrable_trigPoly_term (c k) k]
  simp_rw [integral_const_mul, integral_fourier_haarAddCircle, mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' s 0 c

/-- Parseval for finite trigonometric polynomials. -/
theorem integral_norm_sq_trigPoly [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    ∫ t, ‖trigPoly s c t‖ ^ 2 ∂(haarAddCircle (T := T)) = ∑ k ∈ s, ‖c k‖ ^ 2 := by
  have hpt : ∀ t : AddCircle T, ((‖trigPoly s c t‖ ^ 2 : ℝ) : ℂ) =
      ∑ j ∈ s, ∑ l ∈ s, c j * conj (c l) * fourier (j - l) t := by
    intro t
    push_cast
    rw [← Complex.mul_conj', trigPoly, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← fourier_neg, sub_eq_add_neg, fourier_add]
    ring
  have hint : ∀ j l : ℤ, Integrable (fun t : AddCircle T => c j * conj (c l) * fourier (j - l) t)
      haarAddCircle := fun j l => integrable_trigPoly_term _ _
  have key : ((∫ t, ‖trigPoly s c t‖ ^ 2 ∂(haarAddCircle (T := T)) : ℝ) : ℂ) =
      ((∑ k ∈ s, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint j l]
    simp_rw [integral_finsetSum _ fun l _ => hint _ l, integral_const_mul,
      integral_fourier_haarAddCircle, sub_eq_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Complex.mul_conj']
    push_cast
    exact Finset.sum_congr rfl fun j hj => by simp [hj]
  exact_mod_cast key

theorem trigPoly_eq_add_erase {s : Finset ℤ} (hs : 0 ∈ s) (c : ℤ → ℂ) (t : AddCircle T) :
    trigPoly s c t = c 0 + trigPoly (s.erase 0) c t := by
  rw [trigPoly, trigPoly, ← Finset.add_sum_erase s _ hs, fourier_zero, mul_one]

theorem trigPoly_div (s : Finset ℤ) (c : ℤ → ℂ) (r : ℂ) (t : AddCircle T) :
    trigPoly s (fun k => c k / r) t = trigPoly s c t / r := by
  rw [trigPoly, trigPoly, Finset.sum_div]
  exact Finset.sum_congr rfl fun k _ => div_mul_eq_mul_div _ _ _

end TrigPoly

section Correlation

variable {R : Type*} [CommRing R]

/-- Zero extension of a finite sequence to `ℕ`. -/
def zeroExtend {N : ℕ} (a : Fin N → R) (j : ℕ) : R :=
  if h : j < N then a ⟨j, h⟩ else 0

theorem zeroExtend_of_lt {N : ℕ} (a : Fin N → R) {j : ℕ} (h : j < N) :
    zeroExtend a j = a ⟨j, h⟩ := by
  simp [zeroExtend, h]

theorem zeroExtend_of_le {N : ℕ} (a : Fin N → R) {j : ℕ} (h : N ≤ j) :
    zeroExtend a j = 0 := by
  simp [zeroExtend, Nat.not_lt.2 h]

@[simp] theorem zeroExtend_coe {N : ℕ} (a : Fin N → R) (j : Fin N) :
    zeroExtend a j = a j := zeroExtend_of_lt a j.2

theorem zeroExtend_comp {S : Type*} [CommRing S] (φ : R →+* S) {N : ℕ} (a : Fin N → R) (j : ℕ) :
    zeroExtend (fun k => φ (a k)) j = φ (zeroExtend a j) := by
  unfold zeroExtend
  split_ifs <;> simp

theorem sum_fin_eq_sum_range_zeroExtend {N : ℕ} (a : Fin N → R) (f : ℕ → R → R) :
    ∑ j : Fin N, f j (a j) = ∑ j ∈ range N, f j (zeroExtend a j) := by
  rw [Finset.sum_range]
  simp

/-- The aperiodic autocorrelation `c_k = ∑_{j < N - k} a_j a_{j+k}`. -/
def aperiodicCorr {N : ℕ} (a : Fin N → R) (k : ℕ) : R :=
  ∑ j ∈ range (N - k), zeroExtend a j * zeroExtend a (j + k)

/-- The `Fin` form `∑ j : Fin (N - k), a ⟨j, _⟩ a ⟨j + k, _⟩` used in challenge statements. -/
theorem aperiodicCorr_eq_sum_fin {N : ℕ} (a : Fin N → R) (k : ℕ) :
    aperiodicCorr a k = ∑ j : Fin (N - k), a ⟨j, by omega⟩ * a ⟨j + k, by omega⟩ := by
  rw [aperiodicCorr, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := j.2
  rw [zeroExtend_of_lt a (by omega), zeroExtend_of_lt a (by omega)]

theorem aperiodicCorr_of_le {N : ℕ} (a : Fin N → R) {k : ℕ} (hk : N ≤ k) :
    aperiodicCorr a k = 0 := by
  simp [aperiodicCorr, Nat.sub_eq_zero_of_le hk]

theorem aperiodicCorr_zero {N : ℕ} (a : Fin N → R) :
    aperiodicCorr a 0 = ∑ j : Fin N, a j ^ 2 := by
  rw [aperiodicCorr, Nat.sub_zero, Finset.sum_range]
  simp [sq]

theorem aperiodicCorr_map {S : Type*} [CommRing S] (φ : R →+* S) {N : ℕ} (a : Fin N → R)
    (k : ℕ) : aperiodicCorr (fun j => φ (a j)) k = φ (aperiodicCorr a k) := by
  simp [aperiodicCorr, zeroExtend_comp, map_sum]

/-- The pairs `(j, l)` with `j - l = m` contribute the correlation `c_m`. -/
theorem sum_sum_ite_sub_eq_nat {N : ℕ} (a : Fin N → R) (m : ℕ) :
    ∑ j : Fin N, ∑ l : Fin N, (if (j : ℤ) - l = m then a j * a l else 0) =
      aperiodicCorr a m := by
  rw [Finset.sum_comm]
  have inner : ∀ l : Fin N, ∑ j : Fin N, (if (j : ℤ) - l = m then a j * a l else 0) =
      zeroExtend a (l + m) * zeroExtend a l := by
    intro l
    rw [zeroExtend_coe]
    by_cases h : (l : ℕ) + m < N
    · rw [Finset.sum_eq_single ⟨l + m, h⟩, ite_eq_left (by push_cast; ring), zeroExtend_of_lt a h]
      · intro j _ hj
        refine ite_eq_right fun hc => hj (Fin.ext ?_)
        simp only
        omega
      · simp
    · rw [zeroExtend_of_le a (by omega), zero_mul]
      refine Finset.sum_eq_zero fun j _ => ite_eq_right fun hc => ?_
      have := j.2
      omega
  simp_rw [inner]
  rw [Fin.sum_univ_eq_sum_range (fun l => zeroExtend a (l + m) * zeroExtend a l) N, aperiodicCorr,
    ← Finset.sum_subset (Finset.range_mono (Nat.sub_le N m)) ?_]
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · intro j _ hj
    rw [zeroExtend_of_le a (by simp only [Finset.mem_range] at hj; omega), zero_mul]

/-- The fibre of `(j, l) ↦ j - l` over `k` carries the correlation `c_{|k|}`. -/
theorem aperiodicCorr_natAbs_eq_sum_sum {N : ℕ} (a : Fin N → R) (k : ℤ) :
    aperiodicCorr a k.natAbs =
      ∑ j : Fin N, ∑ l : Fin N, (if (j : ℤ) - l = k then a j * a l else 0) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [Int.natAbs_natCast, sum_sum_ite_sub_eq_nat]
  · rw [Int.natAbs_neg, Int.natAbs_natCast, ← sum_sum_ite_sub_eq_nat, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> first | ring | (exfalso; omega)

/-- Grouping a double sum over `Fin N × Fin N` by the difference `j - l`. -/
theorem sum_sum_mul_eq_sum_aperiodicCorr {N : ℕ} (a : Fin N → R) (w : ℤ → R) :
    ∑ j : Fin N, ∑ l : Fin N, a j * a l * w ((j : ℤ) - l) =
      ∑ k ∈ Ioo (-(N : ℤ)) N, aperiodicCorr a k.natAbs * w k := by
  symm
  simp_rw [aperiodicCorr_natAbs_eq_sum_sum, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm (s := Ioo (-(N : ℤ)) N)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm (s := Ioo (-(N : ℤ)) N)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_ite_eq, ite_eq_left]
  simp only [Finset.mem_Ioo]
  have := j.2
  have := l.2
  omega

/-- Folding a symmetric sum over `(-N, N)`. -/
theorem sum_Ioo_natAbs {M : Type*} [AddCommMonoid M] (f : ℕ → M) {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Ioo (-(N : ℤ)) N, f k.natAbs = f 0 + (∑ k ∈ Ico 1 N, f k + ∑ k ∈ Ico 1 N, f k) := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show Ioo (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ) = {0} by
      ext x; simp only [Finset.mem_Ioo, Finset.mem_singleton]; omega]
    simp
  | succ N hN ih =>
    have hset : Ioo (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert (-(N : ℤ)) (insert (N : ℤ) (Ioo (-(N : ℤ)) N)) := by
      ext x; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Ioo]; omega),
      Finset.sum_insert (by simp only [Finset.mem_Ioo]; omega), ih, Finset.sum_Ico_succ_top hN,
      Int.natAbs_neg, Int.natAbs_natCast]
    abel

/-- `(∑ a_j)^2 = c_0 + 2 ∑_{k ≥ 1} c_k`. -/
theorem sq_sum_eq_aperiodicCorr {N : ℕ} (a : Fin N → R) :
    (∑ j, a j) ^ 2 = aperiodicCorr a 0 + 2 * ∑ k ∈ Ico 1 N, aperiodicCorr a k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [aperiodicCorr]
  have h := sum_sum_mul_eq_sum_aperiodicCorr a (fun _ => 1)
  simp only [mul_one] at h
  rw [sq, Finset.sum_mul_sum, h, sum_Ioo_natAbs (aperiodicCorr a) hN, two_mul]

end Correlation

section Littlewood

variable {T : ℝ} {N : ℕ}

/-- The Littlewood polynomial `P_a(z) = ∑_{k < N} a_k z^k` with real coefficients. -/
def littlewoodPoly (a : Fin N → ℝ) (z : ℂ) : ℂ :=
  ∑ k : Fin N, (a k : ℂ) * z ^ (k : ℕ)

/-- `a` is a `±1` sequence. -/
def IsSigning (a : Fin N → ℝ) : Prop :=
  ∀ k, a k = -1 ∨ a k = 1

theorem IsSigning.sq_eq_one {a : Fin N → ℝ} (ha : IsSigning a) (k : Fin N) : a k ^ 2 = 1 := by
  rcases ha k with h | h <;> simp [h]

theorem IsSigning.abs_eq_one {a : Fin N → ℝ} (ha : IsSigning a) (k : Fin N) : |a k| = 1 := by
  rcases ha k with h | h <;> simp [h]

theorem IsSigning.sum_sq {a : Fin N → ℝ} (ha : IsSigning a) : ∑ k, a k ^ 2 = N := by
  simp [ha.sq_eq_one]

theorem IsSigning.aperiodicCorr_zero {a : Fin N → ℝ} (ha : IsSigning a) :
    aperiodicCorr a 0 = N := by
  rw [TheoremOS.Analysis.aperiodicCorr_zero, ha.sum_sq]

theorem continuous_littlewoodPoly (a : Fin N → ℝ) : Continuous (littlewoodPoly a) := by
  unfold littlewoodPoly
  fun_prop

/-- The trivial bound `‖P z‖ ≤ N` on the unit circle. -/
theorem norm_littlewoodPoly_le {a : Fin N → ℝ} (ha : ∀ k, |a k| ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖littlewoodPoly a z‖ ≤ N := by
  calc ‖littlewoodPoly a z‖ ≤ ∑ k : Fin N, ‖(a k : ℂ) * z ^ (k : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
        rw [norm_mul, norm_pow, hz, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
        exact ha k
    _ = N := by simp

theorem littlewoodPoly_fourier_one (a : Fin N → ℝ) (t : AddCircle T) :
    littlewoodPoly a (fourier 1 t) = ∑ k : Fin N, (a k : ℂ) * fourier (k : ℤ) t := by
  simp_rw [littlewoodPoly, fourier_one_pow]

/-- On the circle, `|P|^2 = ∑_{|k| < N} c_{|k|} e_k`. -/
theorem norm_sq_littlewoodPoly_fourier (a : Fin N → ℝ) (t : AddCircle T) :
    ((‖littlewoodPoly a (fourier 1 t)‖ ^ 2 : ℝ) : ℂ) =
      trigPoly (Ioo (-(N : ℤ)) N) (fun k => ((aperiodicCorr a k.natAbs : ℝ) : ℂ)) t := by
  have hc : ∀ k, aperiodicCorr (fun j => (a j : ℂ)) k = ((aperiodicCorr a k : ℝ) : ℂ) := fun k => by
    simpa using aperiodicCorr_map Complex.ofRealHom a k
  push_cast
  rw [← Complex.mul_conj', littlewoodPoly_fourier_one, map_sum, Finset.sum_mul_sum, trigPoly]
  simp_rw [← hc]
  rw [← sum_sum_mul_eq_sum_aperiodicCorr (fun j => (a j : ℂ)) (fun k => fourier k t)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← fourier_neg, sub_eq_add_neg, fourier_add]
  ring

/-- `∫ |P|^2 = ∑ a_k^2`. -/
theorem integral_norm_sq_littlewoodPoly [Fact (0 < T)] (a : Fin N → ℝ) :
    ∫ t, ‖littlewoodPoly a (fourier 1 t)‖ ^ 2 ∂(haarAddCircle (T := T)) = ∑ k, a k ^ 2 := by
  have key : ((∫ t, ‖littlewoodPoly a (fourier 1 t)‖ ^ 2 ∂(haarAddCircle (T := T)) : ℝ) : ℂ) =
      ((∑ k, a k ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [norm_sq_littlewoodPoly_fourier]
    rw [integral_trigPoly]
    split_ifs with h
    · rw [Int.natAbs_zero, aperiodicCorr_zero]
    · have : N = 0 := by simp only [Finset.mem_Ioo] at h; omega
      subst this
      simp
  exact_mod_cast key

/-- The `L^4` identity `∫ |P|^4 = c_0^2 + 2 ∑_{k=1}^{N-1} c_k^2`. -/
theorem integral_norm_pow_four_littlewoodPoly [Fact (0 < T)] (a : Fin N → ℝ) :
    ∫ t, ‖littlewoodPoly a (fourier 1 t)‖ ^ 4 ∂(haarAddCircle (T := T)) =
      aperiodicCorr a 0 ^ 2 + 2 * ∑ k ∈ Ico 1 N, aperiodicCorr a k ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [littlewoodPoly, aperiodicCorr]
  have hpt : ∀ t : AddCircle T, ‖littlewoodPoly a (fourier 1 t)‖ ^ 4 =
      ‖trigPoly (Ioo (-(N : ℤ)) N) (fun k => ((aperiodicCorr a k.natAbs : ℝ) : ℂ)) t‖ ^ 2 := by
    intro t
    rw [← norm_sq_littlewoodPoly_fourier, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hfold := sum_Ioo_natAbs (fun k => ‖((aperiodicCorr a k : ℝ) : ℂ)‖ ^ 2) hN
  simp_rw [hpt]
  rw [integral_norm_sq_trigPoly, hfold]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end Littlewood

section MeritFactor

variable {T : ℝ} {N : ℕ}

/-- The off-peak correlation energy `E = ∑_{k=1}^{N-1} c_k^2`. -/
def offPeakEnergy (a : Fin N → ℝ) : ℝ :=
  ∑ k ∈ Ico 1 N, aperiodicCorr a k ^ 2

/-- Golay's merit factor `F = N^2 / (2E)`. -/
def meritFactor (a : Fin N → ℝ) : ℝ :=
  (N : ℝ) ^ 2 / (2 * offPeakEnergy a)

theorem inv_meritFactor (a : Fin N → ℝ) :
    (meritFactor a)⁻¹ = 2 * offPeakEnergy a / N ^ 2 :=
  inv_div _ _

theorem IsSigning.integral_norm_pow_four [Fact (0 < T)] {a : Fin N → ℝ} (ha : IsSigning a) :
    ∫ t, ‖littlewoodPoly a (fourier 1 t)‖ ^ 4 ∂(haarAddCircle (T := T)) =
      N ^ 2 + 2 * offPeakEnergy a := by
  rw [integral_norm_pow_four_littlewoodPoly, ha.aperiodicCorr_zero, offPeakEnergy]

theorem continuous_norm_littlewoodPoly_fourier (a : Fin N → ℝ) :
    Continuous fun t : AddCircle T => ‖littlewoodPoly a (fourier 1 t)‖ :=
  ((continuous_littlewoodPoly a).comp (fourier 1).continuous).norm

/-- The variance of `|P|^2 / N` is the inverse merit factor. -/
theorem IsSigning.integral_norm_sq_div_sub_one_sq [Fact (0 < T)] {a : Fin N → ℝ}
    (ha : IsSigning a) (hN : 0 < N) :
    ∫ t, (‖littlewoodPoly a (fourier 1 t)‖ ^ 2 / N - 1) ^ 2 ∂(haarAddCircle (T := T)) =
      2 * offPeakEnergy a / N ^ 2 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hc := continuous_norm_littlewoodPoly_fourier (T := T) a
  have h4 := ha.integral_norm_pow_four (T := T)
  have h2 := integral_norm_sq_littlewoodPoly (T := T) a
  rw [ha.sum_sq] at h2
  have hpt : ∀ t : AddCircle T, (‖littlewoodPoly a (fourier 1 t)‖ ^ 2 / N - 1) ^ 2 =
      1 / N ^ 2 * ‖littlewoodPoly a (fourier 1 t)‖ ^ 4 -
        2 / N * ‖littlewoodPoly a (fourier 1 t)‖ ^ 2 + 1 := fun t => by
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, h4, h2]
  · simp only [integral_const, probReal_univ, one_smul]
    field_simp
    ring
  · exact integrable_haarAddCircle_of_continuous (continuous_const.mul (hc.pow 4))
  · exact integrable_haarAddCircle_of_continuous (continuous_const.mul (hc.pow 2))
  · exact integrable_haarAddCircle_of_continuous
      ((continuous_const.mul (hc.pow 4)).sub (continuous_const.mul (hc.pow 2)))
  · exact integrable_const _

theorem sub_one_sq_le_sq_sub_one_sq {x : ℝ} (hx : 0 ≤ x) : (x - 1) ^ 2 ≤ (x ^ 2 - 1) ^ 2 := by
  nlinarith [mul_nonneg (sq_nonneg (x - 1)) (show 0 ≤ x ^ 2 + 2 * x by positivity)]

/-- The `L^2` distance of `|P| / √N` from `1` is at most the inverse merit factor. -/
theorem IsSigning.integral_norm_div_sqrt_sub_one_sq_le [Fact (0 < T)] {a : Fin N → ℝ}
    (ha : IsSigning a) (hN : 0 < N) :
    ∫ t, (‖littlewoodPoly a (fourier 1 t)‖ / √N - 1) ^ 2 ∂(haarAddCircle (T := T)) ≤
      2 * offPeakEnergy a / N ^ 2 := by
  have hc := continuous_norm_littlewoodPoly_fourier (T := T) a
  rw [← ha.integral_norm_sq_div_sub_one_sq (T := T) hN]
  refine integral_mono (integrable_haarAddCircle_of_continuous (by fun_prop))
    (integrable_haarAddCircle_of_continuous (by fun_prop)) fun t => ?_
  have := sub_one_sq_le_sq_sub_one_sq
    (div_nonneg (norm_nonneg (littlewoodPoly a (fourier 1 t))) (Real.sqrt_nonneg N))
  rwa [div_pow, Real.sq_sqrt (Nat.cast_nonneg N)] at this

/-- Lyapunov's inequality on a probability space: `∫ f^p ≤ (∫ f^q)^(p/q)` for `0 < p ≤ q`. -/
theorem integral_rpow_le_integral_rpow_rpow {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) {p q : ℝ} (hp : 0 < p)
    (hpq : p ≤ q) (hfq : Integrable (fun x => f x ^ q) μ) (hfp : Integrable (fun x => f x ^ p) μ) :
    ∫ x, f x ^ p ∂μ ≤ (∫ x, f x ^ q ∂μ) ^ (p / q) := by
  have hq : 0 < q := hp.trans_le hpq
  have hpt : ∀ x, (f x ^ q) ^ (p / q) = f x ^ p := fun x => by
    rw [← Real.rpow_mul (hf0 x)]
    congr 1
    field_simp
  have h := (Real.concaveOn_rpow (div_pos hp hq).le ((div_le_one hq).2 hpq)).le_map_integral
    (f := fun x => f x ^ q) (μ := μ) (Real.continuous_rpow_const (div_pos hp hq).le).continuousOn
    isClosed_Ici (Filter.Eventually.of_forall fun x => Set.mem_Ici.2 (Real.rpow_nonneg (hf0 x) q))
    hfq (hfp.congr (Filter.Eventually.of_forall fun x => (hpt x).symm))
  simp only [hpt] at h
  exact h

/-- `L^p` flatness for `0 < p ≤ 2` from the merit factor. -/
theorem IsSigning.integral_abs_norm_div_sqrt_sub_one_rpow_le [Fact (0 < T)] {a : Fin N → ℝ}
    (ha : IsSigning a) (hN : 0 < N) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∫ t, |‖littlewoodPoly a (fourier 1 t)‖ / √N - 1| ^ p ∂(haarAddCircle (T := T)) ≤
      (2 * offPeakEnergy a / N ^ 2) ^ (p / 2) := by
  have hc := continuous_norm_littlewoodPoly_fourier (T := T) a
  have hg : Continuous fun t : AddCircle T => |‖littlewoodPoly a (fourier 1 t)‖ / √N - 1| := by
    fun_prop
  have hL := integral_rpow_le_integral_rpow_rpow (μ := haarAddCircle (T := T))
    (f := fun t => |‖littlewoodPoly a (fourier 1 t)‖ / √N - 1|) (fun t => abs_nonneg _) hp hp2
    (integrable_haarAddCircle_of_continuous (hg.rpow_const fun _ => Or.inr (by norm_num)))
    (integrable_haarAddCircle_of_continuous (hg.rpow_const fun _ => Or.inr hp.le))
  refine hL.trans (Real.rpow_le_rpow (integral_nonneg fun t => by positivity) ?_ (by positivity))
  calc ∫ t, |‖littlewoodPoly a (fourier 1 t)‖ / √N - 1| ^ (2 : ℝ) ∂(haarAddCircle (T := T)) =
        ∫ t, (‖littlewoodPoly a (fourier 1 t)‖ / √N - 1) ^ 2 ∂(haarAddCircle (T := T)) := by
        simp_rw [Real.rpow_two, sq_abs]
    _ ≤ _ := ha.integral_norm_div_sqrt_sub_one_sq_le hN

/-- Some point of the unit circle has `√N ≤ ‖P z‖`. -/
theorem IsSigning.exists_sqrt_le_norm {a : Fin N → ℝ} (ha : IsSigning a) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ √N ≤ ‖littlewoodPoly a z‖ := by
  obtain ⟨t, ht⟩ := exists_integral_le_apply (T := 1)
    (g := fun t => ‖littlewoodPoly a (fourier 1 t)‖ ^ 2)
    ((continuous_norm_littlewoodPoly_fourier (T := 1) a).pow 2)
  rw [integral_norm_sq_littlewoodPoly, ha.sum_sq] at ht
  refine ⟨fourier 1 t, norm_fourier_apply 1 t, ?_⟩
  simpa [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt ht

/-- Some point of the unit circle has `‖P z‖ ≤ √N`. -/
theorem IsSigning.exists_norm_le_sqrt {a : Fin N → ℝ} (ha : IsSigning a) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ‖littlewoodPoly a z‖ ≤ √N := by
  obtain ⟨t, ht⟩ := exists_apply_le_integral (T := 1)
    (g := fun t => ‖littlewoodPoly a (fourier 1 t)‖ ^ 2)
    ((continuous_norm_littlewoodPoly_fourier (T := 1) a).pow 2)
  rw [integral_norm_sq_littlewoodPoly, ha.sum_sq] at ht
  refine ⟨fourier 1 t, norm_fourier_apply 1 t, ?_⟩
  simpa [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt ht

end MeritFactor

end

end TheoremOS.Analysis
