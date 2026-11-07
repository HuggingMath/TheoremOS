import Mathlib

/-!
# Cofinite subspaces and asymptotic moduli of a seminorm

For a real normed space `X`, a closed subspace of finite codimension is *cofinite*
(`IsCofinite F`). For a function `N : X → ℝ` (usually an equivalent seminorm), a point `x`, a
parameter `t` and a cofinite `F`, the inner infima are
`asympOneSidedInner N t x F = inf {N(x + t y) - 1 : y ∈ F, N y = 1}`,
`asympAveragedInner N t x F = inf {(N(x + t y) + N(x - t y))/2 - 1 : y ∈ F, 1 ≤ N y}` and its unit
version `asympAveragedUnitInner` (directions with `N y = 1`); taking `sup` over cofinite `F` gives
`asympOneSided`/`asympAveraged`, and `inf` over `N x = 1` gives the moduli
`asympOneSidedModulus`/`asympAveragedModulus`. Contents: `⊤`, finite intersections and kernels of
continuous functionals (more generally of continuous maps to finite-dimensional spaces) are
cofinite; in an infinite-dimensional space every cofinite subspace contains `N`-unit vectors when
`a‖·‖ ≤ N`; Hahn–Banach for a seminorm `N ≤ b‖·‖` (`exists_clm_eq_one_le`); the generic bounds
`max 0 (|t| - 2) ≤ one-sided ≤ |t|` and `max 0 (|t| - 1) ≤ averaged ≤ |t|` at every unit point and
for the moduli; the convexity step `N(x + c y) + N(x - c y) ≤ N(x + y) + N(x - y)` for `c ∈ [0, 1]`
and the identity `asympAveragedInner = asympAveragedUnitInner` for seminorms; antitonicity of the
inner infima in `F`.

Sources: W. B. Johnson, J. Lindenstrauss, D. Preiss and G. Schechtman, Almost Fréchet
differentiability of Lipschitz mappings between infinite-dimensional Banach spaces, Proc. London
Math. Soc. 84 (2002) 711–746, Section 2 (asymptotic moduli); V. D. Milman, Geometric theory of
Banach spaces II, Russian Math. Surveys 26 (1971) 79–163, Section 4.6; M. Fabian, P. Habala,
P. Hájek, V. Montesinos and V. Zizler, *Banach Space Theory*, Springer CMS Books, 2011, Theorem 2.1
(Hahn–Banach) and Section 2.3 (closed subspaces of finite codimension). Textbook material; nothing
here is specific to a benchmark problem.

Bridges: a set `{F | IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)}` is
`{F | IsCofinite F}` by `rfl`. Nested `sInf`/`sSup`/`sInf` definitions of the form
`sInf {r | ∃ x, N x = 1 ∧ r = sSup {a | ∃ F, IsCofinite F ∧ a = sInf {b | ∃ y, y ∈ F ∧ N y = 1 ∧
b = N (x + t • y) - 1}}}` are `asympOneSidedModulus N t` by `rfl` (also with `∃ F ∈ S`, with the
pair `∃ y ∈ F` and with `averagedIncrement` unfolded); the averaged versions with `1 ≤ N y` and
`/ 2` likewise. A supremum over `Set.range` of a function on the subtype of cofinite subspaces is
rewritten with `sSup_range_cofinite`. `((2 : ℕ) : ℝ)` is `2` by `Nat.cast_ofNat`.
-/

namespace TheoremOS.Analysis

open Set

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A closed linear subspace of finite codimension. -/
def IsCofinite (F : Submodule ℝ X) : Prop :=
  IsClosed (F : Set X) ∧ FiniteDimensional ℝ (X ⧸ F)

namespace IsCofinite

theorem top : IsCofinite (⊤ : Submodule ℝ X) := ⟨isClosed_univ, inferInstance⟩

theorem inf {F G : Submodule ℝ X} (hF : IsCofinite F) (hG : IsCofinite G) : IsCofinite (F ⊓ G) := by
  refine ⟨by simpa using hF.1.inter hG.1, ?_⟩
  have := hF.2
  have := hG.2
  have hker : (F.mkQ.prod G.mkQ).ker = F ⊓ G := by
    rw [LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  exact LinearEquiv.finiteDimensional
    ((Submodule.quotEquivOfEq _ _ hker).symm.trans (F.mkQ.prod G.mkQ).quotKerEquivRange).symm

/-- The kernel of a continuous linear map to a finite-dimensional space is cofinite. -/
theorem ker {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ℓ : X →L[ℝ] E) : IsCofinite (LinearMap.ker (ℓ : X →ₗ[ℝ] E)) :=
  ⟨ℓ.isClosed_ker, LinearEquiv.finiteDimensional (ℓ : X →ₗ[ℝ] E).quotKerEquivRange.symm⟩

theorem ker_functional (ℓ : X →L[ℝ] ℝ) : IsCofinite (LinearMap.ker (ℓ : X →ₗ[ℝ] ℝ)) := ker ℓ

/-- In an infinite-dimensional space a cofinite subspace is nonzero. -/
theorem ne_bot (hX : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X} (hF : IsCofinite F) :
    F ≠ ⊥ := by
  rintro rfl
  have := hF.2
  exact hX (LinearEquiv.finiteDimensional (Submodule.quotEquivOfEqBot ⊥ rfl))

/-- In an infinite-dimensional space a cofinite subspace contains `N`-unit vectors when
`a ‖·‖ ≤ N` with `0 < a`. -/
theorem exists_unit (hX : ¬ FiniteDimensional ℝ X) {F : Submodule ℝ X} (hF : IsCofinite F)
    (N : Seminorm ℝ X) {a : ℝ} (ha : 0 < a) (hN : ∀ x, a * ‖x‖ ≤ N x) :
    ∃ y ∈ F, N y = 1 := by
  obtain ⟨y, hyF, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hF.ne_bot hX)
  have hNy : 0 < N y := lt_of_lt_of_le (mul_pos ha (norm_pos_iff.mpr hy0)) (hN y)
  refine ⟨(N y)⁻¹ • y, F.smul_mem _ hyF, ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hNy, inv_mul_cancel₀ hNy.ne']

end IsCofinite

/-- Supremum over the subtype of cofinite subspaces, rewritten as a supremum over a set. -/
theorem sSup_range_cofinite (g : Submodule ℝ X → ℝ) :
    sSup (Set.range fun F : {F : Submodule ℝ X // IsClosed (F : Set X) ∧
      FiniteDimensional ℝ (X ⧸ F)} => g F.val) = sSup {a | ∃ F, IsCofinite F ∧ a = g F} := by
  congr 1
  ext a
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.val, F.property, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨⟨F, hF⟩, rfl⟩

/-- Hahn–Banach for a seminorm `N ≤ b ‖·‖`: a continuous functional `ℓ ≤ N` with `ℓ x = 1`. -/
theorem exists_clm_eq_one_le (N : Seminorm ℝ X) {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) {x : X}
    (hx : N x = 1) : ∃ ℓ : X →L[ℝ] ℝ, ℓ x = 1 ∧ ∀ z, ℓ z ≤ N z := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨g, hg, hgN⟩ := exists_extension_of_le_sublinear
    (LinearPMap.mkSpanSingleton x (1 : ℝ) hx0) N
    (fun c hc z => by rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc])
    (fun z w => map_add_le_add N z w) (by
      rintro ⟨z, hz⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      rw [LinearPMap.mkSpanSingleton'_apply]
      simp only [RingHom.id_apply, smul_eq_mul, mul_one, map_smul_eq_mul, hx, Real.norm_eq_abs]
      exact le_abs_self c)
  have hgx : g x = 1 := by
    have := hg ⟨x, Submodule.mem_span_singleton_self x⟩
    rw [this]
    exact LinearPMap.mkSpanSingleton_apply ℝ ℝ hx0 1
  have hbound : ∀ z, ‖g z‖ ≤ b * ‖z‖ := by
    intro z
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := (hgN (-z)).trans (hNb (-z))
      rw [map_neg, norm_neg] at this
      linarith
    · exact (hgN z).trans (hNb z)
  exact ⟨g.mkContinuous b hbound, by simpa using hgx, fun z => by simpa using hgN z⟩

section Moduli

/-- `inf {N(x + t y) - 1 : y ∈ F, N y = 1}`. -/
def asympOneSidedInner (N : X → ℝ) (t : ℝ) (x : X) (F : Submodule ℝ X) : ℝ :=
  sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1}

/-- `sup` of `asympOneSidedInner` over cofinite subspaces. -/
def asympOneSided (N : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sSup {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympOneSidedInner N t x F}

/-- The one-sided asymptotic modulus: `inf` of `asympOneSided` over `N x = 1`. -/
def asympOneSidedModulus (N : X → ℝ) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r = asympOneSided N t x}

/-- `inf {(N(x + t y) + N(x - t y))/2 - 1 : y ∈ F, 1 ≤ N y}`. -/
def asympAveragedInner (N : X → ℝ) (t : ℝ) (x : X) (F : Submodule ℝ X) : ℝ :=
  sInf {b | ∃ y : X, y ∈ F ∧ 1 ≤ N y ∧ b = (N (x + t • y) + N (x - t • y)) / 2 - 1}

/-- The same infimum over directions with `N y = 1`. -/
def asympAveragedUnitInner (N : X → ℝ) (t : ℝ) (x : X) (F : Submodule ℝ X) : ℝ :=
  sInf {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = (N (x + t • y) + N (x - t • y)) / 2 - 1}

/-- `sup` of `asympAveragedInner` over cofinite subspaces. -/
def asympAveraged (N : X → ℝ) (t : ℝ) (x : X) : ℝ :=
  sSup {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympAveragedInner N t x F}

/-- The averaged asymptotic (midpoint) modulus. -/
def asympAveragedModulus (N : X → ℝ) (t : ℝ) : ℝ :=
  sInf {r | ∃ x : X, N x = 1 ∧ r = asympAveraged N t x}

/-- An `sInf` of a set all of whose elements are `≤ c` with `0 ≤ c` is `≤ c`, whether or not the
set is empty. -/
theorem sInf_le_of_forall_mem_le {s : Set ℝ} {c : ℝ} (hs : BddBelow s) (hc : 0 ≤ c)
    (h : ∀ b ∈ s, b ≤ c) : sInf s ≤ c := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · simpa using hc
  · exact (csInf_le hs hb).trans (h b hb)

variable (N : Seminorm ℝ X)

theorem bddBelow_asympOneSidedInner (t : ℝ) (x : X) (F : Submodule ℝ X) :
    BddBelow {b | ∃ y : X, y ∈ F ∧ N y = 1 ∧ b = N (x + t • y) - 1} :=
  ⟨-1, by rintro b ⟨y, -, -, rfl⟩; linarith [apply_nonneg N (x + t • y)]⟩

theorem asympOneSidedInner_le_abs {t : ℝ} {x : X} (hx : N x = 1) (F : Submodule ℝ X) :
    asympOneSidedInner N t x F ≤ |t| :=
  sInf_le_of_forall_mem_le (bddBelow_asympOneSidedInner N t x F) (abs_nonneg t) (by
    rintro b ⟨y, -, hy, rfl⟩
    have := map_add_le_add N x (t • y)
    rw [map_smul_eq_mul, Real.norm_eq_abs, hx, hy] at this
    linarith)

/-- On the kernel of a functional `ℓ ≤ N` with `ℓ x = 1` the inner infimum is nonnegative. -/
theorem asympOneSidedInner_ker_nonneg {x : X} {ℓ : X →L[ℝ] ℝ} (hℓx : ℓ x = 1) (hℓ : ∀ z, ℓ z ≤ N z)
    (t : ℝ) (F : Submodule ℝ X) :
    0 ≤ asympOneSidedInner N t x (F ⊓ LinearMap.ker (ℓ : X →ₗ[ℝ] ℝ)) := by
  refine Real.sInf_nonneg ?_
  rintro b ⟨y, hy, -, rfl⟩
  have hy0 : ℓ y = 0 := (Submodule.mem_inf.mp hy).2
  have := hℓ (x + t • y)
  simp only [map_add, map_smul, hℓx, hy0, smul_eq_mul, mul_zero, add_zero] at this
  linarith

theorem bddAbove_asympOneSided {t : ℝ} {x : X} (hx : N x = 1) :
    BddAbove {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympOneSidedInner (⇑N) t x F} :=
  ⟨|t|, by rintro a ⟨F, -, rfl⟩; exact asympOneSidedInner_le_abs N hx F⟩

theorem asympOneSidedInner_le {t : ℝ} {x : X} (hx : N x = 1) {F : Submodule ℝ X}
    (hF : IsCofinite F) : asympOneSidedInner N t x F ≤ asympOneSided N t x :=
  le_csSup (bddAbove_asympOneSided N hx) ⟨F, hF, rfl⟩

theorem asympOneSided_le_abs {t : ℝ} {x : X} (hx : N x = 1) : asympOneSided N t x ≤ |t| :=
  Real.sSup_le (by rintro a ⟨F, -, rfl⟩; exact asympOneSidedInner_le_abs N hx F) (abs_nonneg t)

/-- `0 ≤ D(x, t)` at an `N`-unit point when `N ≤ b ‖·‖` (Hahn–Banach). -/
theorem asympOneSided_nonneg {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) {t : ℝ} {x : X} (hx : N x = 1) :
    0 ≤ asympOneSided N t x := by
  obtain ⟨ℓ, hℓx, hℓ⟩ := exists_clm_eq_one_le N hNb hx
  have h := asympOneSidedInner_ker_nonneg N hℓx hℓ t ⊤
  rw [top_inf_eq] at h
  exact h.trans (asympOneSidedInner_le N hx (IsCofinite.ker_functional ℓ))

/-- `|t| - 2 ≤ inf` over all unit directions, by the triangle inequality. -/
theorem abs_sub_two_le_asympOneSidedInner_top {t : ℝ} {x : X} (hx : N x = 1) :
    |t| - 2 ≤ asympOneSidedInner N t x ⊤ := by
  refine le_csInf ⟨_, x, Submodule.mem_top, hx, rfl⟩ ?_
  rintro b ⟨y, -, hy, rfl⟩
  have := map_sub_le_add N (x + t • y) x
  rw [add_sub_cancel_left, map_smul_eq_mul, Real.norm_eq_abs, hy, hx] at this
  linarith

/-- Generic bounds `max 0 (|t| - 2) ≤ D(x, t) ≤ |t|` at an `N`-unit point. -/
theorem max_le_asympOneSided {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) {t : ℝ} {x : X} (hx : N x = 1) :
    max 0 (|t| - 2) ≤ asympOneSided N t x :=
  max_le (asympOneSided_nonneg N hNb hx)
    ((abs_sub_two_le_asympOneSidedInner_top N hx).trans (asympOneSidedInner_le N hx IsCofinite.top))

theorem asympOneSidedModulus_le_abs (t : ℝ) : asympOneSidedModulus N t ≤ |t| :=
  sInf_le_of_forall_mem_le ⟨|t| - 2, by
      rintro r ⟨x, hx, rfl⟩
      exact (abs_sub_two_le_asympOneSidedInner_top N hx).trans
        (asympOneSidedInner_le N hx IsCofinite.top)⟩
    (abs_nonneg t) (by rintro r ⟨x, hx, rfl⟩; exact asympOneSided_le_abs N hx)

theorem asympOneSidedModulus_nonneg {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) (t : ℝ) :
    0 ≤ asympOneSidedModulus N t :=
  Real.sInf_nonneg (by rintro r ⟨x, hx, rfl⟩; exact asympOneSided_nonneg N hNb hx)

/-- Generic lower bound for the modulus, given one `N`-unit vector. -/
theorem max_le_asympOneSidedModulus {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) (hX : ∃ x, N x = 1)
    (t : ℝ) : max 0 (|t| - 2) ≤ asympOneSidedModulus N t := by
  obtain ⟨x₀, hx₀⟩ := hX
  exact le_csInf ⟨_, x₀, hx₀, rfl⟩ (by rintro r ⟨x, hx, rfl⟩; exact max_le_asympOneSided N hNb hx)

/-- A larger subspace has a smaller inner infimum (when the smaller one has unit vectors). -/
theorem asympOneSidedInner_anti {t : ℝ} {x : X} {F G : Submodule ℝ X} (hFG : F ≤ G)
    (hF : ∃ y ∈ F, N y = 1) : asympOneSidedInner N t x G ≤ asympOneSidedInner N t x F := by
  obtain ⟨y, hyF, hy⟩ := hF
  exact csInf_le_csInf (bddBelow_asympOneSidedInner N t x G) ⟨_, y, hyF, hy, rfl⟩
    (by rintro b ⟨z, hz, hz1, rfl⟩; exact ⟨z, hFG hz, hz1, rfl⟩)

/-- Two sets of reals with `B ⊆ A`, every element of `A` above some element of `B` and `A`
bounded below have the same infimum (also when they are empty). -/
theorem sInf_eq_of_subset_of_forall_exists_le {A B : Set ℝ} (hA : BddBelow A) (hBA : B ⊆ A)
    (h : ∀ a ∈ A, ∃ b ∈ B, b ≤ a) : sInf A = sInf B := by
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have : A = ∅ := by
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      obtain ⟨b, hb, -⟩ := h a ha
      exact hb
    rw [this]
  · exact le_antisymm (csInf_le_csInf hA hB hBA)
      (le_csInf (hB.mono hBA) fun a ha => by
        obtain ⟨b, hb, hba⟩ := h a ha
        exact (csInf_le (hA.mono hBA) hb).trans hba)

/-- Convexity step: `N(x + c y) + N(x - c y) ≤ N(x + y) + N(x - y)` for `0 ≤ c ≤ 1`. -/
theorem add_smul_add_sub_smul_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (x y : X) :
    N (x + c • y) + N (x - c • y) ≤ N (x + y) + N (x - y) := by
  have e1 : x + c • y = ((1 + c) / 2) • (x + y) + ((1 - c) / 2) • (x - y) := by module
  have e2 : x - c • y = ((1 - c) / 2) • (x + y) + ((1 + c) / 2) • (x - y) := by module
  have h1 := map_add_le_add N (((1 + c) / 2) • (x + y)) (((1 - c) / 2) • (x - y))
  have h2 := map_add_le_add N (((1 - c) / 2) • (x + y)) (((1 + c) / 2) • (x - y))
  rw [← e1] at h1
  rw [← e2] at h2
  simp only [map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 + c) / 2),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (1 - c) / 2)] at h1 h2
  linarith

theorem bddBelow_asympAveragedInner (P : X → Prop) (t : ℝ) (x : X) (F : Submodule ℝ X) :
    BddBelow {b | ∃ y : X, y ∈ F ∧ P y ∧ b = (N (x + t • y) + N (x - t • y)) / 2 - 1} :=
  ⟨-1, by
    rintro b ⟨y, -, -, rfl⟩
    linarith [apply_nonneg N (x + t • y), apply_nonneg N (x - t • y)]⟩

/-- For a seminorm, directions with `1 ≤ N y` and with `N y = 1` give the same averaged
infimum. -/
theorem asympAveragedInner_eq_unit (t : ℝ) (x : X) (F : Submodule ℝ X) :
    asympAveragedInner N t x F = asympAveragedUnitInner N t x F := by
  refine sInf_eq_of_subset_of_forall_exists_le (bddBelow_asympAveragedInner N _ t x F)
    (by rintro b ⟨y, hyF, hy, rfl⟩; exact ⟨y, hyF, hy.ge, rfl⟩) ?_
  rintro b ⟨y, hyF, hy, rfl⟩
  have hpos : 0 < N y := lt_of_lt_of_le one_pos hy
  refine ⟨_, ⟨(N y)⁻¹ • y, F.smul_mem _ hyF, ?_, rfl⟩, ?_⟩
  · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
  · have := add_smul_add_sub_smul_le N (inv_nonneg.mpr hpos.le) (inv_le_one_of_one_le₀ hy) x
      (t • y)
    rw [smul_comm (N y)⁻¹ t y] at this
    linarith

theorem asympAveragedInner_le_abs {t : ℝ} {x : X} (hx : N x = 1) (F : Submodule ℝ X) :
    asympAveragedInner N t x F ≤ |t| := by
  rw [asympAveragedInner_eq_unit]
  refine sInf_le_of_forall_mem_le (bddBelow_asympAveragedInner N _ t x F) (abs_nonneg t) ?_
  rintro b ⟨y, -, hy, rfl⟩
  have h1 := map_add_le_add N x (t • y)
  have h2 := map_sub_le_add N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, hx, hy] at h1 h2
  linarith

theorem asympAveragedInner_ker_nonneg {x : X} {ℓ : X →L[ℝ] ℝ} (hℓx : ℓ x = 1)
    (hℓ : ∀ z, ℓ z ≤ N z) (t : ℝ) (F : Submodule ℝ X) :
    0 ≤ asympAveragedInner N t x (F ⊓ LinearMap.ker (ℓ : X →ₗ[ℝ] ℝ)) := by
  refine Real.sInf_nonneg ?_
  rintro b ⟨y, hy, -, rfl⟩
  have hy0 : ℓ y = 0 := (Submodule.mem_inf.mp hy).2
  have h1 := hℓ (x + t • y)
  have h2 := hℓ (x - t • y)
  simp only [map_add, map_sub, map_smul, hℓx, hy0, smul_eq_mul, mul_zero, add_zero,
    sub_zero] at h1 h2
  linarith

/-- `|t| - 1 ≤ inf` over all directions, by the triangle inequality. -/
theorem abs_sub_one_le_asympAveragedInner_top {t : ℝ} {x : X} (hx : N x = 1) :
    |t| - 1 ≤ asympAveragedInner N t x ⊤ := by
  refine le_csInf ⟨_, x, Submodule.mem_top, hx.ge, rfl⟩ ?_
  rintro b ⟨y, -, hy, rfl⟩
  have := map_sub_le_add N (x + t • y) (x - t • y)
  rw [show x + t • y - (x - t • y) = (2 * t) • y by module, map_smul_eq_mul, Real.norm_eq_abs,
    abs_mul, abs_two] at this
  have hty : |t| ≤ |t| * N y := le_mul_of_one_le_right (abs_nonneg t) hy
  linarith

theorem bddAbove_asympAveraged {t : ℝ} {x : X} (hx : N x = 1) :
    BddAbove {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympAveragedInner (⇑N) t x F} :=
  ⟨|t|, by rintro a ⟨F, -, rfl⟩; exact asympAveragedInner_le_abs N hx F⟩

theorem asympAveragedInner_le {t : ℝ} {x : X} (hx : N x = 1) {F : Submodule ℝ X}
    (hF : IsCofinite F) : asympAveragedInner N t x F ≤ asympAveraged N t x :=
  le_csSup (bddAbove_asympAveraged N hx) ⟨F, hF, rfl⟩

theorem asympAveraged_le_abs {t : ℝ} {x : X} (hx : N x = 1) : asympAveraged N t x ≤ |t| :=
  Real.sSup_le (by rintro a ⟨F, -, rfl⟩; exact asympAveragedInner_le_abs N hx F) (abs_nonneg t)

/-- `0 ≤ H(x, t)` at an `N`-unit point when `N ≤ b ‖·‖` (Hahn–Banach). -/
theorem asympAveraged_nonneg {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) {t : ℝ} {x : X} (hx : N x = 1) :
    0 ≤ asympAveraged N t x := by
  obtain ⟨ℓ, hℓx, hℓ⟩ := exists_clm_eq_one_le N hNb hx
  have h := asympAveragedInner_ker_nonneg N hℓx hℓ t ⊤
  rw [top_inf_eq] at h
  exact h.trans (asympAveragedInner_le N hx (IsCofinite.ker_functional ℓ))

/-- Generic bounds `max 0 (|t| - 1) ≤ H(x, t) ≤ |t|` at an `N`-unit point. -/
theorem max_le_asympAveraged {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) {t : ℝ} {x : X} (hx : N x = 1) :
    max 0 (|t| - 1) ≤ asympAveraged N t x :=
  max_le (asympAveraged_nonneg N hNb hx)
    ((abs_sub_one_le_asympAveragedInner_top N hx).trans (asympAveragedInner_le N hx IsCofinite.top))

theorem asympAveragedModulus_le_abs (t : ℝ) : asympAveragedModulus N t ≤ |t| :=
  sInf_le_of_forall_mem_le ⟨|t| - 1, by
      rintro r ⟨x, hx, rfl⟩
      exact (abs_sub_one_le_asympAveragedInner_top N hx).trans
        (asympAveragedInner_le N hx IsCofinite.top)⟩
    (abs_nonneg t) (by rintro r ⟨x, hx, rfl⟩; exact asympAveraged_le_abs N hx)

theorem asympAveragedModulus_nonneg {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) (t : ℝ) :
    0 ≤ asympAveragedModulus N t :=
  Real.sInf_nonneg (by rintro r ⟨x, hx, rfl⟩; exact asympAveraged_nonneg N hNb hx)

theorem max_le_asympAveragedModulus {b : ℝ} (hNb : ∀ z, N z ≤ b * ‖z‖) (hX : ∃ x, N x = 1)
    (t : ℝ) : max 0 (|t| - 1) ≤ asympAveragedModulus N t := by
  obtain ⟨x₀, hx₀⟩ := hX
  exact le_csInf ⟨_, x₀, hx₀, rfl⟩ (by rintro r ⟨x, hx, rfl⟩; exact max_le_asympAveraged N hNb hx)

theorem asympAveragedInner_anti {t : ℝ} {x : X} {F G : Submodule ℝ X} (hFG : F ≤ G)
    (hF : ∃ y ∈ F, 1 ≤ N y) : asympAveragedInner N t x G ≤ asympAveragedInner N t x F := by
  obtain ⟨y, hyF, hy⟩ := hF
  exact csInf_le_csInf (bddBelow_asympAveragedInner N _ t x G) ⟨_, y, hyF, hy, rfl⟩
    (by rintro b ⟨z, hz, hz1, rfl⟩; exact ⟨z, hFG hz, hz1, rfl⟩)

/-- Unit-direction form of `asympAveraged`. -/
theorem asympAveraged_eq_unit (t : ℝ) (x : X) :
    asympAveraged N t x =
      sSup {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympAveragedUnitInner N t x F} := by
  simp only [asympAveraged, asympAveragedInner_eq_unit]

/-- Unit-direction form of the averaged modulus. -/
theorem asympAveragedModulus_eq_unit (t : ℝ) :
    asympAveragedModulus N t = sInf {r | ∃ x : X, N x = 1 ∧ r =
      sSup {a | ∃ F : Submodule ℝ X, IsCofinite F ∧ a = asympAveragedUnitInner N t x F}} := by
  simp only [asympAveragedModulus, asympAveraged_eq_unit]

end Moduli

end

end TheoremOS.Analysis
