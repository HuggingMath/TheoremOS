import Mathlib

/-!
# Translative covering and packing numbers

For sets `A B` in an additive group, `IsTranslateCover A B c` says the translates `c j + B`
(`j : Fin M`) cover `A`, `translateCoveringNumber A B` is the least such `M` (`0` when `A` has no
finite cover), and `translatePackingNumber A B` is the largest size of a finite `T ⊆ A` whose
pairwise differences avoid `B`. Contents: monotonicity, translation and linear invariance,
submultiplicativity `N(A, C) ≤ N(A, B) N(B, C)`; finite covers of compact sets by neighbourhoods
of `0`; maximal packings are covers, so `N(A, B) ≤ M(A, B)`, and `M(A, B) ≤ N(A, C)` when
`C - C ⊆ B`; the volumetric bounds for a Haar measure `μ` on a finite-dimensional real normed
space: `μ A ≤ N(A, B) μ B`, and for `K` convex and symmetric
`M(A, K) μ(½K) ≤ μ(A + ½K)`, `N(A, K) μ(½K) ≤ μ(A + ½K)`; for a convex symmetric body `K`,
`ε^{-n} ≤ N(K, εK) ≤ (1 + 2/ε)^n` with `n` the dimension, and the same bounds for norm balls
`N(B(0,R), B(0,r))`; on `ι → ℝ`, the polar `{y | ∀ x ∈ K, ∑ x_i y_i ≤ 1}` and the duality of the
cube `{|x_i| ≤ 1}` and the cross-polytope `{∑ |y_i| ≤ 1}` with their volumes `2^n` and `2^n/n!`.

Sources: C. A. Rogers, *Packing and Covering*, Cambridge Tracts 54, 1964, Chapter 1;
R. Vershynin, *High-Dimensional Probability*, Cambridge University Press, 2018, Section 4.2
(nets, covering and packing numbers, volumetric bounds); G. Pisier, *The Volume of Convex Bodies
and Banach Space Geometry*, Cambridge Tracts 94, 1989, Lemma 4.10; S. Artstein-Avidan,
A. Giannopoulos and V. D. Milman, *Asymptotic Geometric Analysis, Part I*, AMS, 2015, Section 4.1;
R. Schneider, *Convex Bodies: the Brunn–Minkowski Theory*, 2nd ed., Cambridge, 2014, Section 1.6
(polar bodies). Textbook material; nothing here is specific to a benchmark problem.

Bridges: `∀ x ∈ A, ∃ j, x - c j ∈ B` is `IsTranslateCover A B c` by `Iff.rfl`, and
`sInf {M : ℕ | ∃ c : Fin M → E, ∀ x ∈ A, ∃ j, x - c j ∈ B}` is `translateCoveringNumber A B` by
`rfl`. On `ι → ℝ` with the sup norm, `{x | ∀ i, |x i| ≤ 1}` is `supBall ι` and equals
`Metric.closedBall 0 1` (`supBall_eq_closedBall`); a polar written with `∑ i, x i * y i ≤ 1` is
`coordPolar K` by `rfl`.
-/

namespace TheoremOS.Geometry

open MeasureTheory Set Pointwise Bornology

noncomputable section

section Group

variable {E : Type*} [AddCommGroup E]

/-- The translates `c j + B`, `j : Fin M`, cover `A`. -/
def IsTranslateCover {M : ℕ} (A B : Set E) (c : Fin M → E) : Prop :=
  ∀ x ∈ A, ∃ j, x - c j ∈ B

/-- `A` is covered by finitely many translates of `B`. -/
def TranslateCoverable (A B : Set E) : Prop :=
  ∃ M : ℕ, ∃ c : Fin M → E, IsTranslateCover A B c

/-- The **translative covering number**: the least number of translates of `B` covering `A`
(`0` when there is no finite cover). -/
def translateCoveringNumber (A B : Set E) : ℕ :=
  sInf {M : ℕ | ∃ c : Fin M → E, IsTranslateCover A B c}

/-- `T` is a **`B`-packing** of `A`: a finite subset of `A` whose pairwise differences avoid
`B`. -/
def IsTranslatePacking (A B : Set E) (T : Finset E) : Prop :=
  (T : Set E) ⊆ A ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x - y ∉ B

/-- The **translative packing number**: the largest size of a `B`-packing of `A` (`0` when the
sizes are unbounded). -/
def translatePackingNumber (A B : Set E) : ℕ :=
  sSup {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m}

lemma IsTranslateCover.translateCoveringNumber_le {M : ℕ} {A B : Set E} {c : Fin M → E}
    (h : IsTranslateCover A B c) : translateCoveringNumber A B ≤ M :=
  Nat.sInf_le ⟨c, h⟩

lemma exists_isTranslateCover_translateCoveringNumber {A B : Set E}
    (h : TranslateCoverable A B) :
    ∃ c : Fin (translateCoveringNumber A B) → E, IsTranslateCover A B c := by
  obtain ⟨M, c, hc⟩ := h
  exact Nat.sInf_mem (s := {M : ℕ | ∃ c : Fin M → E, IsTranslateCover A B c}) ⟨M, c, hc⟩

/-- A finite set of centres covering `A` bounds the covering number by its size. -/
lemma translateCoveringNumber_le_card {A B : Set E} (t : Finset E)
    (ht : ∀ x ∈ A, ∃ y ∈ t, x - y ∈ B) : translateCoveringNumber A B ≤ t.card := by
  refine IsTranslateCover.translateCoveringNumber_le (c := fun j => (t.equivFin.symm j : E)) ?_
  intro x hx
  obtain ⟨y, hy, hxy⟩ := ht x hx
  exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

lemma translateCoverable_of_finset {A B : Set E} (t : Finset E)
    (ht : ∀ x ∈ A, ∃ y ∈ t, x - y ∈ B) : TranslateCoverable A B :=
  ⟨t.card, fun j => (t.equivFin.symm j : E), fun x hx => by
    obtain ⟨y, hy, hxy⟩ := ht x hx
    exact ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩⟩

lemma IsTranslateCover.mono {M : ℕ} {A A' B B' : Set E} {c : Fin M → E}
    (h : IsTranslateCover A B c) (hA : A' ⊆ A) (hB : B ⊆ B') : IsTranslateCover A' B' c :=
  fun x hx => (h x (hA hx)).imp fun _ hj => hB hj

lemma TranslateCoverable.mono {A A' B B' : Set E} (h : TranslateCoverable A B) (hA : A' ⊆ A)
    (hB : B ⊆ B') : TranslateCoverable A' B' :=
  let ⟨M, c, hc⟩ := h; ⟨M, c, hc.mono hA hB⟩

lemma translateCoveringNumber_mono_left {A A' B : Set E} (h : TranslateCoverable A B)
    (hA : A' ⊆ A) : translateCoveringNumber A' B ≤ translateCoveringNumber A B :=
  let ⟨_, hc⟩ := exists_isTranslateCover_translateCoveringNumber h
  (hc.mono hA le_rfl).translateCoveringNumber_le

lemma translateCoveringNumber_mono_right {A B B' : Set E} (h : TranslateCoverable A B)
    (hB : B ⊆ B') : translateCoveringNumber A B' ≤ translateCoveringNumber A B :=
  let ⟨_, hc⟩ := exists_isTranslateCover_translateCoveringNumber h
  (hc.mono le_rfl hB).translateCoveringNumber_le

lemma translateCoveringNumber_empty (B : Set E) : translateCoveringNumber (∅ : Set E) B = 0 :=
  Nat.eq_zero_of_le_zero (IsTranslateCover.translateCoveringNumber_le
    (c := (Fin.elim0 : Fin 0 → E)) fun _ hx => hx.elim)

/-- Covering is transitive: covers of `A` by `B` and of `B` by `C` compose. -/
lemma IsTranslateCover.trans {M N : ℕ} {A B C : Set E} {c : Fin M → E} {d : Fin N → E}
    (h₁ : IsTranslateCover A B c) (h₂ : IsTranslateCover B C d) :
    IsTranslateCover A C fun k => c (finProdFinEquiv.symm k).1 + d (finProdFinEquiv.symm k).2 := by
  intro x hx
  obtain ⟨j, hj⟩ := h₁ x hx
  obtain ⟨k, hk⟩ := h₂ _ hj
  exact ⟨finProdFinEquiv (j, k), by simpa [sub_add_eq_sub_sub] using hk⟩

/-- **Submultiplicativity**: `N(A, C) ≤ N(A, B) N(B, C)`. -/
lemma translateCoveringNumber_le_mul {A B C : Set E} (hAB : TranslateCoverable A B)
    (hBC : TranslateCoverable B C) :
    translateCoveringNumber A C ≤ translateCoveringNumber A B * translateCoveringNumber B C :=
  let ⟨_, hc⟩ := exists_isTranslateCover_translateCoveringNumber hAB
  let ⟨_, hd⟩ := exists_isTranslateCover_translateCoveringNumber hBC
  (hc.trans hd).translateCoveringNumber_le

lemma translateCoverable_trans {A B C : Set E} (hAB : TranslateCoverable A B)
    (hBC : TranslateCoverable B C) : TranslateCoverable A C :=
  let ⟨_, _, hc⟩ := hAB
  let ⟨_, _, hd⟩ := hBC
  ⟨_, _, hc.trans hd⟩

/-- Covering numbers are invariant under additive automorphisms. -/
lemma translateCoveringNumber_image_addEquiv {F : Type*} [AddCommGroup F] (e : E ≃+ F)
    (A B : Set E) : translateCoveringNumber (e '' A) (e '' B) = translateCoveringNumber A B := by
  unfold translateCoveringNumber
  congr 1
  ext M
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => e.symm (c j), fun x hx => ?_⟩
    obtain ⟨j, b, hb, hbx⟩ := hc (e x) ⟨x, hx, rfl⟩
    refine ⟨j, ?_⟩
    have : x - e.symm (c j) = b := by
      apply e.injective
      rw [map_sub, e.apply_symm_apply, hbx]
    exact this ▸ hb
  · rintro ⟨c, hc⟩
    refine ⟨fun j => e (c j), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := hc x hx
    exact ⟨j, x - c j, hj, map_sub e x (c j)⟩

lemma translateCoverable_image_addEquiv_iff {F : Type*} [AddCommGroup F] (e : E ≃+ F)
    {A B : Set E} : TranslateCoverable (e '' A) (e '' B) ↔ TranslateCoverable A B := by
  constructor
  · rintro ⟨M, c, hc⟩
    refine ⟨M, fun j => e.symm (c j), fun x hx => ?_⟩
    obtain ⟨j, b, hb, hbx⟩ := hc (e x) ⟨x, hx, rfl⟩
    refine ⟨j, ?_⟩
    have : x - e.symm (c j) = b := by
      apply e.injective
      rw [map_sub, e.apply_symm_apply, hbx]
    exact this ▸ hb
  · rintro ⟨M, c, hc⟩
    refine ⟨M, fun j => e (c j), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := hc x hx
    exact ⟨j, x - c j, hj, map_sub e x (c j)⟩

/-- Covering numbers are invariant under translating the covered set. -/
lemma translateCoveringNumber_vadd (a : E) (A B : Set E) :
    translateCoveringNumber (a +ᵥ A) B = translateCoveringNumber A B := by
  unfold translateCoveringNumber
  congr 1
  ext M
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨fun j => c j - a, fun x hx => ?_⟩
    obtain ⟨j, hj⟩ := hc (a + x) ⟨x, hx, rfl⟩
    exact ⟨j, by rwa [sub_sub_eq_add_sub, add_comm x a]⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun j => a + c j, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨j, hj⟩ := hc x hx
    refine ⟨j, ?_⟩
    change a + x - (a + c j) ∈ B
    rwa [add_sub_add_left_eq_sub]

lemma IsTranslatePacking.empty (A B : Set E) : IsTranslatePacking A B ∅ :=
  ⟨by simp, by simp⟩

lemma IsTranslatePacking.mono {A A' B B' : Set E} {T : Finset E} (h : IsTranslatePacking A B T)
    (hA : A ⊆ A') (hB : B' ⊆ B) : IsTranslatePacking A' B' T :=
  ⟨h.1.trans hA, fun x hx y hy hxy hm => h.2 x hx y hy hxy (hB hm)⟩

/-- A point of `A` far from every point of a packing extends it, when `B` is symmetric. -/
lemma IsTranslatePacking.insert [DecidableEq E] {A B : Set E} {T : Finset E} (h : IsTranslatePacking A B T)
    (hB : ∀ z, z ∈ B → -z ∈ B) {x : E} (hx : x ∈ A) (hxT : ∀ y ∈ T, x - y ∉ B) :
    IsTranslatePacking A B (insert x T) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_insert]
    exact Set.insert_subset hx h.1
  · intro y hy z hz hyz
    rw [Finset.mem_insert] at hy hz
    rcases hy with rfl | hy <;> rcases hz with rfl | hz
    · exact absurd rfl hyz
    · exact hxT z hz
    · intro hm
      exact hxT y hy (by simpa using hB _ hm)
    · exact h.2 y hy z hz hyz

/-- A packing of maximal size is a cover, when `B` is symmetric and contains `0`. -/
lemma IsTranslatePacking.covers_of_maximal {A B : Set E} {T : Finset E}
    (h : IsTranslatePacking A B T) (h0 : (0 : E) ∈ B) (hB : ∀ z, z ∈ B → -z ∈ B)
    (hmax : ∀ T' : Finset E, IsTranslatePacking A B T' → T'.card ≤ T.card) :
    ∀ x ∈ A, ∃ y ∈ T, x - y ∈ B := by
  classical
  intro x hx
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hxT : x ∉ T := fun hxT => hne x hxT (by simpa using h0)
  have := hmax _ (h.insert hB hx hne)
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

lemma exists_isTranslatePacking_card_eq {A B : Set E}
    (hbdd : BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m}) :
    ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = translatePackingNumber A B :=
  Nat.sSup_mem (s := {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m})
    ⟨0, ∅, IsTranslatePacking.empty A B, rfl⟩ hbdd

lemma IsTranslatePacking.card_le_translatePackingNumber {A B : Set E} {T : Finset E}
    (h : IsTranslatePacking A B T)
    (hbdd : BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m}) :
    T.card ≤ translatePackingNumber A B :=
  le_csSup hbdd ⟨T, h, rfl⟩

/-- `N(A, B) ≤ M(A, B)` for `B` symmetric and containing `0`, when packing sizes are bounded. -/
lemma translateCoveringNumber_le_translatePackingNumber {A B : Set E} (h0 : (0 : E) ∈ B)
    (hB : ∀ z, z ∈ B → -z ∈ B)
    (hbdd : BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m}) :
    translateCoveringNumber A B ≤ translatePackingNumber A B := by
  obtain ⟨T, hT, hcard⟩ := exists_isTranslatePacking_card_eq hbdd
  rw [← hcard]
  exact translateCoveringNumber_le_card T (hT.covers_of_maximal h0 hB fun T' hT' =>
    hcard ▸ hT'.card_le_translatePackingNumber hbdd)

lemma translateCoverable_of_bddAbove {A B : Set E} (h0 : (0 : E) ∈ B)
    (hB : ∀ z, z ∈ B → -z ∈ B)
    (hbdd : BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m}) :
    TranslateCoverable A B := by
  obtain ⟨T, hT, hcard⟩ := exists_isTranslatePacking_card_eq hbdd
  exact translateCoverable_of_finset T (hT.covers_of_maximal h0 hB fun T' hT' =>
    hcard ▸ hT'.card_le_translatePackingNumber hbdd)

/-- A `B`-packing has at most `N(A, C)` points when `C - C ⊆ B`. -/
lemma IsTranslatePacking.card_le_of_isTranslateCover {A B C : Set E} {T : Finset E} {N : ℕ}
    {c : Fin N → E} (hT : IsTranslatePacking A B T) (hc : IsTranslateCover A C c)
    (hC : ∀ u ∈ C, ∀ v ∈ C, u - v ∈ B) : T.card ≤ N := by
  classical
  have hmem : ∀ x : T, ∃ j, (x : E) - c j ∈ C := fun x => hc x (hT.1 x.2)
  choose f hf using hmem
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hne' : (x : E) ≠ y := fun h => hne (Subtype.ext h)
    refine hT.2 x x.2 y y.2 hne' ?_
    have := hC _ (hf x) _ (hxy ▸ hf y)
    rwa [sub_sub_sub_cancel_right] at this
  simpa using Fintype.card_le_of_injective f hinj

/-- `M(A, B) ≤ N(A, C)` when `C - C ⊆ B`. -/
lemma translatePackingNumber_le_translateCoveringNumber {A B C : Set E}
    (hAC : TranslateCoverable A C) (hC : ∀ u ∈ C, ∀ v ∈ C, u - v ∈ B) :
    translatePackingNumber A B ≤ translateCoveringNumber A C := by
  obtain ⟨c, hc⟩ := exists_isTranslateCover_translateCoveringNumber hAC
  refine csSup_le' ?_
  rintro _ ⟨T, hT, rfl⟩
  exact hT.card_le_of_isTranslateCover hc hC

lemma bddAbove_packing_of_translateCoverable {A B C : Set E} (hAC : TranslateCoverable A C)
    (hC : ∀ u ∈ C, ∀ v ∈ C, u - v ∈ B) :
    BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A B T ∧ T.card = m} := by
  obtain ⟨c, hc⟩ := exists_isTranslateCover_translateCoveringNumber hAC
  refine ⟨translateCoveringNumber A C, ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  exact hT.card_le_of_isTranslateCover hc hC

end Group

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For `K` convex and symmetric, differences of points of `½K` lie in `K`. -/
lemma sub_mem_of_mem_half {K : Set E} (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K) :
    ∀ u ∈ (2 : ℝ)⁻¹ • K, ∀ v ∈ (2 : ℝ)⁻¹ • K, u - v ∈ K := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  have := hK ha (hsymm b hb) (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)
  simpa [smul_neg, ← sub_eq_add_neg] using this

/-- A nonempty convex symmetric set contains `0`. -/
lemma zero_mem_of_convex_symm {K : Set E} (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K)
    (hne : K.Nonempty) : (0 : E) ∈ K := by
  obtain ⟨a, ha⟩ := hne
  simpa using sub_mem_of_mem_half hK hsymm _ ⟨a, ha, rfl⟩ _ ⟨a, ha, rfl⟩

/-- For `K` convex and symmetric, the translates `x + ½K` of the points of a `K`-packing are
pairwise disjoint. -/
lemma IsTranslatePacking.pairwiseDisjoint_half {A K : Set E} {T : Finset E}
    (hT : IsTranslatePacking A K T) (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K) :
    (T : Set E).PairwiseDisjoint fun x => x +ᵥ (2 : ℝ)⁻¹ • K := by
  intro x hx y hy hxy
  rw [Function.onFun, Set.disjoint_left]
  rintro z ⟨u, hu, rfl⟩ ⟨v, hv, hvz⟩
  refine hT.2 x hx y hy hxy ?_
  have hvz' : y + v = x + u := hvz
  have : x - y = v - u := by
    rw [sub_eq_sub_iff_add_eq_add, ← hvz', add_comm]
  rw [this]
  exact sub_mem_of_mem_half hK hsymm v hv u hu

/-- Covering numbers are invariant under a common nonzero dilation. -/
lemma translateCoveringNumber_smul {c : ℝ} (hc : c ≠ 0) (A B : Set E) :
    translateCoveringNumber (c • A) (c • B) = translateCoveringNumber A B := by
  have h := translateCoveringNumber_image_addEquiv
    (LinearEquiv.smulOfNeZero ℝ E c hc).toAddEquiv A B
  simpa [Set.image_smul] using h

end Module

section Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The **volumetric lower bound**: `μ A ≤ M μ B` for a cover of `A` by `M` translates of `B`. -/
lemma IsTranslateCover.measure_le {M : ℕ} {A B : Set E} {c : Fin M → E}
    (h : IsTranslateCover A B c) : μ A ≤ M * μ B := by
  have hsub : A ⊆ ⋃ j, c j +ᵥ B := fun x hx => by
    obtain ⟨j, hj⟩ := h x hx
    exact Set.mem_iUnion.2 ⟨j, x - c j, hj, by simp [vadd_eq_add]⟩
  calc μ A ≤ μ (⋃ j, c j +ᵥ B) := measure_mono hsub
    _ ≤ ∑ j, μ (c j +ᵥ B) := measure_iUnion_fintype_le μ _
    _ = M * μ B := by simp [measure_vadd]

lemma measure_le_translateCoveringNumber_mul {A B : Set E} (h : TranslateCoverable A B) :
    μ A ≤ translateCoveringNumber A B * μ B :=
  let ⟨_, hc⟩ := exists_isTranslateCover_translateCoveringNumber h
  hc.measure_le μ

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A compact set is covered by finitely many translates of any neighbourhood of `0`. -/
lemma translateCoverable_of_isCompact {A B : Set E} (hA : IsCompact A)
    (hB : B ∈ nhds (0 : E)) : TranslateCoverable A B := by
  classical
  obtain ⟨t, -, hcover⟩ := hA.elim_nhds_subcover (fun c => (fun x => x - c) ⁻¹' B)
    fun c _ => (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using hB)
  refine translateCoverable_of_finset t fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  exact ⟨y, hy, hxy⟩

/-- **Volumetric packing bound**: for `K` convex and symmetric, a `K`-packing `T` of `A` has
`|T| μ(½K) ≤ μ(A + ½K)`. -/
lemma IsTranslatePacking.card_mul_measure_le {A K : Set E} {T : Finset E}
    (hT : IsTranslatePacking A K T) (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K) :
    T.card * μ ((2 : ℝ)⁻¹ • K) ≤ μ (A + (2 : ℝ)⁻¹ • K) := by
  have hdisj := hT.pairwiseDisjoint_half hK hsymm
  have hsub : (⋃ x ∈ T, x +ᵥ (2 : ℝ)⁻¹ • K) ⊆ A + (2 : ℝ)⁻¹ • K := by
    refine Set.iUnion₂_subset fun x hx => ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨x, hT.1 hx, u, hu, by simp [vadd_eq_add]⟩
  calc (T.card : ENNReal) * μ ((2 : ℝ)⁻¹ • K) = ∑ x ∈ T, μ (x +ᵥ (2 : ℝ)⁻¹ • K) := by
        simp [measure_vadd]
    _ = μ (⋃ x ∈ T, x +ᵥ (2 : ℝ)⁻¹ • K) := by
        rw [measure_biUnion_finset₀]
        · exact hdisj.mono' fun _ _ h => h.aedisjoint
        · exact fun x _ => ((hK.smul _).vadd x).nullMeasurableSet μ
    _ ≤ μ (A + (2 : ℝ)⁻¹ • K) := measure_mono hsub

/-- The volumetric packing bound in real form: `|T| ≤ μ(A + ½K) / μ(½K)`. -/
lemma IsTranslatePacking.card_le_measure_div {A K : Set E} {T : Finset E}
    (hT : IsTranslatePacking A K T) (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K)
    (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0) (hfin : μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤) :
    (T.card : ℝ) ≤ (μ (A + (2 : ℝ)⁻¹ • K)).toReal / (μ ((2 : ℝ)⁻¹ • K)).toReal := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hfin' : μ ((2 : ℝ)⁻¹ • K) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin ?_
    calc μ ((2 : ℝ)⁻¹ • K) = μ (x +ᵥ (2 : ℝ)⁻¹ • K) := (measure_vadd μ x _).symm
      _ ≤ μ (A + (2 : ℝ)⁻¹ • K) := measure_mono (by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨x, hT.1 hx, u, hu, rfl⟩)
  have hreal := ENNReal.toReal_mono hfin (hT.card_mul_measure_le μ hK hsymm)
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  rw [le_div_iff₀ (ENNReal.toReal_pos hpos hfin')]
  exact hreal

lemma bddAbove_packing_of_measure {A K : Set E} (hK : Convex ℝ K) (hsymm : ∀ z, z ∈ K → -z ∈ K)
    (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0) (hfin : μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤) :
    BddAbove {m : ℕ | ∃ T : Finset E, IsTranslatePacking A K T ∧ T.card = m} := by
  refine ⟨⌊(μ (A + (2 : ℝ)⁻¹ • K)).toReal / (μ ((2 : ℝ)⁻¹ • K)).toReal⌋₊, ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  exact Nat.le_floor (hT.card_le_measure_div μ hK hsymm hpos hfin)

/-- **Volumetric bound for the packing number**: `M(A, K) ≤ μ(A + ½K) / μ(½K)` for `K` convex
and symmetric. -/
theorem translatePackingNumber_le_measure_div {A K : Set E} (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0)
    (hfin : μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤) :
    (translatePackingNumber A K : ℝ) ≤
      (μ (A + (2 : ℝ)⁻¹ • K)).toReal / (μ ((2 : ℝ)⁻¹ • K)).toReal := by
  obtain ⟨T, hT, hcard⟩ := exists_isTranslatePacking_card_eq
    (bddAbove_packing_of_measure μ hK hsymm hpos hfin)
  rw [← hcard]
  exact hT.card_le_measure_div μ hK hsymm hpos hfin

omit [BorelSpace E] [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
lemma nonempty_of_measure_half_ne_zero {K : Set E} (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0) :
    K.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  simp [h] at hpos

/-- A convex symmetric `K` with `μ(½K) > 0` and `μ(A + ½K) < ∞` covers `A` with finitely many
translates. -/
lemma translateCoverable_of_measure {A K : Set E} (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0)
    (hfin : μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤) : TranslateCoverable A K :=
  translateCoverable_of_bddAbove
    (zero_mem_of_convex_symm hK hsymm (nonempty_of_measure_half_ne_zero μ hpos)) hsymm
    (bddAbove_packing_of_measure μ hK hsymm hpos hfin)

/-- **Volumetric bound for the covering number**: `N(A, K) ≤ μ(A + ½K) / μ(½K)` for `K` convex
and symmetric. -/
theorem translateCoveringNumber_le_measure_div {A K : Set E} (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hpos : μ ((2 : ℝ)⁻¹ • K) ≠ 0)
    (hfin : μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤) :
    (translateCoveringNumber A K : ℝ) ≤
      (μ (A + (2 : ℝ)⁻¹ • K)).toReal / (μ ((2 : ℝ)⁻¹ • K)).toReal :=
  (Nat.cast_le.2 (translateCoveringNumber_le_translatePackingNumber
    (zero_mem_of_convex_symm hK hsymm (nonempty_of_measure_half_ne_zero μ hpos)) hsymm
    (bddAbove_packing_of_measure μ hK hsymm hpos hfin))).trans
    (translatePackingNumber_le_measure_div μ hK hsymm hpos hfin)

lemma measure_half_ne_zero {K : Set E} (hint : (interior K).Nonempty) :
    μ ((2 : ℝ)⁻¹ • K) ≠ 0 := by
  rw [Measure.addHaar_smul_of_nonneg μ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  exact mul_ne_zero (by simp) (Measure.measure_pos_of_nonempty_interior μ hint).ne'

omit [BorelSpace E] in
lemma measure_add_half_ne_top {A K : Set E} (hA : IsBounded A) (hKb : IsBounded K) :
    μ (A + (2 : ℝ)⁻¹ • K) ≠ ⊤ :=
  (hA.add (hKb.smul₀ _)).measure_lt_top.ne

/-- The covering and packing numbers of a bounded set by a convex symmetric bounded set with
nonempty interior are finite and satisfy the volumetric bounds. -/
lemma translateCoverable_of_isBounded {A K : Set E} (hA : IsBounded A) (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hKb : IsBounded K) (hint : (interior K).Nonempty) :
    TranslateCoverable A K :=
  translateCoverable_of_measure Measure.addHaar hK hsymm (measure_half_ne_zero _ hint)
    (measure_add_half_ne_top _ hA hKb)

lemma toReal_measure_smul {s : ℝ} (hs : 0 ≤ s) (K : Set E) :
    (μ (s • K)).toReal = s ^ Module.finrank ℝ E * (μ K).toReal := by
  rw [Measure.addHaar_smul_of_nonneg μ hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- **Covering a convex body by its dilates**: for `K` convex, symmetric, bounded with nonempty
interior and `ε > 0`, `N(K, εK) ≤ (1 + 2/ε)^n`, `n = dim E`. -/
theorem translateCoveringNumber_smul_self_le {K : Set E} (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hKb : IsBounded K) (hint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (translateCoveringNumber K (ε • K) : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ E := by
  let μ : Measure E := Measure.addHaar
  have hsymm' : ∀ z, z ∈ ε • K → -z ∈ ε • K := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, hsymm a ha, smul_neg ε a⟩
  have hint' : (interior (ε • K)).Nonempty := by
    rw [interior_smul₀ hε.ne']
    exact hint.smul_set
  have h := translateCoveringNumber_le_measure_div μ (hK.smul ε) hsymm'
    (measure_half_ne_zero μ hint') (measure_add_half_ne_top μ hKb (hKb.smul₀ ε))
  have hhalf : (2 : ℝ)⁻¹ • ε • K = (ε / 2) • K := by
    rw [smul_smul, inv_mul_eq_div]
  have hsum : K + (ε / 2) • K = (1 + ε / 2) • K := by
    rw [hK.add_smul zero_le_one (by positivity), one_smul]
  have hK0 : (μ K).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
    ⟨(Measure.measure_pos_of_nonempty_interior μ hint).ne', hKb.measure_lt_top.ne⟩
  rw [hhalf, hsum, toReal_measure_smul μ (by positivity), toReal_measure_smul μ (by positivity),
    mul_div_mul_right _ _ hK0, ← div_pow] at h
  convert h using 2
  field_simp
  ring

/-- The matching lower bound `ε^{-n} ≤ N(K, εK)`. -/
theorem le_translateCoveringNumber_smul_self {K : Set E} (hK : Convex ℝ K)
    (hsymm : ∀ z, z ∈ K → -z ∈ K) (hKb : IsBounded K) (hint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    (1 / ε) ^ Module.finrank ℝ E ≤ (translateCoveringNumber K (ε • K) : ℝ) := by
  let μ : Measure E := Measure.addHaar
  have hsymm' : ∀ z, z ∈ ε • K → -z ∈ ε • K := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨-a, hsymm a ha, smul_neg ε a⟩
  have hint' : (interior (ε • K)).Nonempty := by
    rw [interior_smul₀ hε.ne']
    exact hint.smul_set
  have hcov := translateCoverable_of_isBounded hKb (hK.smul ε) hsymm' (hKb.smul₀ ε) hint'
  have h := measure_le_translateCoveringNumber_mul μ hcov
  have hfin : μ (ε • K) ≠ ⊤ := (hKb.smul₀ ε).measure_lt_top.ne
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, toReal_measure_smul μ hε.le] at hreal
  have hK0 : 0 < (μ K).toReal := ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior μ hint).ne' hKb.measure_lt_top.ne
  have h1 : 1 ≤ (translateCoveringNumber K (ε • K) : ℝ) * ε ^ Module.finrank ℝ E := by
    nlinarith
  rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
  exact h1

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma closedBall_neg_mem {r : ℝ} : ∀ z, z ∈ Metric.closedBall (0 : E) r →
    -z ∈ Metric.closedBall (0 : E) r := fun z hz => by
  simpa [mem_closedBall_zero_iff, norm_neg] using hz

lemma toReal_measure_closedBall {s : ℝ} (hs : 0 ≤ s) :
    (μ (Metric.closedBall (0 : E) s)).toReal =
      s ^ Module.finrank ℝ E * (μ (Metric.closedBall (0 : E) 1)).toReal := by
  rw [← toReal_measure_smul μ hs, smul_unitClosedBall_of_nonneg hs]

omit [BorelSpace E] in
lemma toReal_measure_closedBall_one_pos : 0 < (μ (Metric.closedBall (0 : E) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos μ 0 one_pos).ne'
    measure_closedBall_lt_top.ne

/-- **Covering a ball by smaller balls**: `N(B(0,R), B(0,r)) ≤ (1 + 2R/r)^n`. -/
theorem translateCoveringNumber_closedBall_le {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    (translateCoveringNumber (Metric.closedBall (0 : E) R) (Metric.closedBall (0 : E) r) : ℝ) ≤
      (1 + 2 * R / r) ^ Module.finrank ℝ E := by
  let μ : Measure E := Measure.addHaar
  have hhalf : (2 : ℝ)⁻¹ • Metric.closedBall (0 : E) r = Metric.closedBall 0 (r / 2) := by
    rw [smul_closedBall _ _ hr.le, smul_zero, Real.norm_eq_abs, abs_of_pos (by norm_num),
      inv_mul_eq_div]
  have hpos : μ ((2 : ℝ)⁻¹ • Metric.closedBall (0 : E) r) ≠ 0 := by
    rw [hhalf]
    exact (Metric.measure_closedBall_pos μ 0 (by positivity)).ne'
  have h := translateCoveringNumber_le_measure_div μ (A := Metric.closedBall (0 : E) R)
    (convex_closedBall 0 r) closedBall_neg_mem hpos
    (measure_add_half_ne_top μ Metric.isBounded_closedBall Metric.isBounded_closedBall)
  rw [hhalf, closedBall_add_closedBall hR (by positivity), add_zero,
    toReal_measure_closedBall μ (s := R + r / 2) (by positivity),
    toReal_measure_closedBall μ (s := r / 2) (by positivity),
    mul_div_mul_right _ _ (toReal_measure_closedBall_one_pos μ).ne', ← div_pow] at h
  convert h using 2
  field_simp
  ring

/-- The matching lower bound `(R/r)^n ≤ N(B(0,R), B(0,r))`. -/
theorem le_translateCoveringNumber_closedBall {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) :
    (R / r) ^ Module.finrank ℝ E ≤
      (translateCoveringNumber (Metric.closedBall (0 : E) R) (Metric.closedBall (0 : E) r) : ℝ) := by
  let μ : Measure E := Measure.addHaar
  have hcov := translateCoverable_of_isCompact (isCompact_closedBall (0 : E) R)
    (Metric.closedBall_mem_nhds (0 : E) hr)
  have h := measure_le_translateCoveringNumber_mul μ hcov
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne) h
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, toReal_measure_closedBall μ hR,
    toReal_measure_closedBall μ hr.le, ← mul_assoc] at hreal
  have h1 := le_of_mul_le_mul_right hreal (toReal_measure_closedBall_one_pos μ)
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact h1

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A translative cover by `ε`-balls is an `ε`-cover in the sense of `Metric.IsCover`, so the
external covering number is at most the translative one. -/
lemma externalCoveringNumber_le_translateCoveringNumber {A : Set E} {ε : NNReal}
    (h : TranslateCoverable A (Metric.closedBall (0 : E) ε)) :
    Metric.externalCoveringNumber ε A ≤ translateCoveringNumber A (Metric.closedBall 0 ε) := by
  obtain ⟨c, hc⟩ := exists_isTranslateCover_translateCoveringNumber h
  refine (Metric.IsCover.externalCoveringNumber_le_encard (C := Set.range c) ?_).trans ?_
  · rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro x hx
    obtain ⟨j, hj⟩ := hc x hx
    exact Set.mem_iUnion₂.2 ⟨c j, ⟨j, rfl⟩, by simpa [dist_eq_norm] using hj⟩
  · calc (Set.range c).encard ≤ (Set.univ : Set (Fin _)).encard := by
          rw [← Set.image_univ]
          exact Set.encard_image_le c _
      _ = _ := by simp

end Measure

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- The cube `{x | ∀ i, |x i| ≤ 1}`, the closed unit ball of the sup norm on `ι → ℝ`. -/
def supBall (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, |x i| ≤ 1}

/-- The cross-polytope `{y | ∑ i, |y i| ≤ 1}`, the closed unit ball of `ℓ¹` on `ι → ℝ`. -/
def crossPolytope (ι : Type*) [Fintype ι] : Set (ι → ℝ) := {y | ∑ i, |y i| ≤ 1}

/-- The polar `{y | ∀ x ∈ K, ∑ i, x i * y i ≤ 1}` of `K ⊆ ι → ℝ` for the coordinate pairing. -/
def coordPolar (K : Set (ι → ℝ)) : Set (ι → ℝ) := {y | ∀ x ∈ K, ∑ i, x i * y i ≤ 1}

omit [Fintype ι] in
lemma supBall_eq_closedBall [Fintype ι] : supBall ι = Metric.closedBall (0 : ι → ℝ) 1 := by
  ext x
  simp [supBall, pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]

lemma coordPolar_anti {K L : Set (ι → ℝ)} (h : K ⊆ L) : coordPolar L ⊆ coordPolar K :=
  fun _ hy x hx => hy x (h hx)

lemma zero_mem_coordPolar (K : Set (ι → ℝ)) : (0 : ι → ℝ) ∈ coordPolar K := fun _ _ => by simp

lemma convex_coordPolar (K : Set (ι → ℝ)) : Convex ℝ (coordPolar K) := by
  intro y hy z hz a b ha hb hab x hx
  have hsum : ∑ i, x i * (a • y + b • z) i = a * ∑ i, x i * y i + b * ∑ i, x i * z i := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  nlinarith [hy x hx, hz x hx]

lemma isClosed_coordPolar (K : Set (ι → ℝ)) : IsClosed (coordPolar K) := by
  have : coordPolar K = ⋂ x ∈ K, {y : ι → ℝ | ∑ i, x i * y i ≤ 1} := by
    ext y
    simp [coordPolar]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i))
      continuous_const

lemma neg_mem_coordPolar {K : Set (ι → ℝ)} (hsymm : ∀ z, z ∈ K → -z ∈ K) :
    ∀ y, y ∈ coordPolar K → -y ∈ coordPolar K := fun y hy x hx => by
  simpa using hy (-x) (hsymm x hx)

/-- `(cK)° = c⁻¹ K°` for `c ≠ 0`. -/
lemma coordPolar_smul {c : ℝ} (hc : c ≠ 0) (K : Set (ι → ℝ)) :
    coordPolar (c • K) = c⁻¹ • coordPolar K := by
  ext y
  rw [Set.mem_inv_smul_set_iff₀ hc]
  constructor
  · intro hy x hx
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hy (c • x) ⟨x, hx, rfl⟩
  · rintro hy _ ⟨x, hx, rfl⟩
    simpa [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hy x hx

/-- `|x i| ≤ 1` for all `i` gives `∑ x_i y_i ≤ ∑ |y_i|`. -/
lemma sum_mul_le_sum_abs {x y : ι → ℝ} (hx : x ∈ supBall ι) : ∑ i, x i * y i ≤ ∑ i, |y i| :=
  Finset.sum_le_sum fun i _ => (le_abs_self _).trans (by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hx i))

/-- The polar of the cube is the cross-polytope. -/
theorem coordPolar_supBall : coordPolar (supBall ι) = crossPolytope ι := by
  classical
  ext y
  constructor
  · intro hy
    have hs : (fun i => if 0 ≤ y i then (1 : ℝ) else -1) ∈ supBall ι := fun i => by
      dsimp only
      split_ifs <;> simp
    have h := hy _ hs
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) h
    split_ifs with hi
    · rw [abs_of_nonneg hi, one_mul]
    · rw [abs_of_neg (not_le.1 hi), neg_one_mul]
  · intro hy x hx
    exact (sum_mul_le_sum_abs hx).trans hy

/-- The polar of the cross-polytope is the cube. -/
theorem coordPolar_crossPolytope : coordPolar (crossPolytope ι) = supBall ι := by
  classical
  ext y
  constructor
  · intro hy i
    have hsingle : ∀ t : ℝ, |t| ≤ 1 → Pi.single i t ∈ crossPolytope ι := fun t ht => by
      change ∑ j, |Pi.single i t j| ≤ 1
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simpa using ht
    have hp := hsingle 1 (by simp)
    have hm := hsingle (-1) (by simp)
    have h1 := hy _ hp
    have h2 := hy _ hm
    simp only [Pi.single_apply, ite_mul, one_mul, neg_one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1 h2
    exact abs_le.2 ⟨by linarith, h1⟩
  · intro hy x hx
    calc ∑ i, x i * y i = ∑ i, y i * x i := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ ≤ ∑ i, |x i| := sum_mul_le_sum_abs hy
      _ ≤ 1 := hx

/-- The cube has volume `2^n`. -/
theorem volume_supBall : volume (supBall ι) = ENNReal.ofReal (2 ^ Fintype.card ι) := by
  rw [supBall_eq_closedBall, Real.volume_pi_closedBall 0 zero_le_one, mul_one]

/-- The cross-polytope has volume `2^n / n!`. -/
theorem volume_crossPolytope [Nonempty ι] :
    volume (crossPolytope ι) = ENNReal.ofReal (2 ^ Fintype.card ι / (Fintype.card ι).factorial) := by
  have hset : {x : ι → ℝ | (∑ i, |x i| ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ 1} = crossPolytope ι := by
    ext x
    simp [crossPolytope]
  have h := MeasureTheory.volume_sum_rpow_le (ι := ι) le_rfl 1
  rw [hset] at h
  rw [h, ENNReal.ofReal_one, one_pow, one_mul]
  congr 1
  simp only [div_one, one_add_one_eq_two, Real.Gamma_two, mul_one]
  rw [← Real.Gamma_nat_eq_factorial]

/-- On `ι → ℝ` with the sup norm, the cube is a convex symmetric body; in particular
`N(cube, ε cube) ≤ (1 + 2/ε)^n` (`translateCoveringNumber_smul_self_le`). -/
lemma convex_supBall : Convex ℝ (supBall ι) := by
  rw [supBall_eq_closedBall]
  exact convex_closedBall 0 1

omit [Fintype ι] in
lemma neg_mem_supBall : ∀ z, z ∈ supBall ι → -z ∈ supBall ι := fun z hz i => by
  simpa using hz i

lemma isBounded_supBall : IsBounded (supBall ι) := by
  rw [supBall_eq_closedBall]
  exact Metric.isBounded_closedBall

lemma interior_supBall_nonempty : (interior (supBall ι)).Nonempty := by
  rw [supBall_eq_closedBall]
  exact ⟨0, mem_interior_iff_mem_nhds.2 (Metric.closedBall_mem_nhds 0 one_pos)⟩

lemma convex_crossPolytope : Convex ℝ (crossPolytope ι) := by
  rw [← coordPolar_supBall]
  exact convex_coordPolar _

lemma neg_mem_crossPolytope : ∀ z, z ∈ crossPolytope ι → -z ∈ crossPolytope ι := fun z hz => by
  simpa [crossPolytope] using hz

lemma crossPolytope_subset_supBall : crossPolytope ι ⊆ supBall ι := fun y hy i =>
  (Finset.single_le_sum (fun j _ => abs_nonneg (y j)) (Finset.mem_univ i)).trans hy

lemma isBounded_crossPolytope : IsBounded (crossPolytope ι) :=
  isBounded_supBall.subset crossPolytope_subset_supBall

lemma closedBall_subset_crossPolytope [Nonempty ι] :
    Metric.closedBall (0 : ι → ℝ) (Fintype.card ι : ℝ)⁻¹ ⊆ crossPolytope ι := by
  intro y hy
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)] at hy
  calc ∑ i, |y i| ≤ ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ :=
        Finset.sum_le_sum fun i _ => by simpa [Real.norm_eq_abs] using hy i
    _ = 1 := by simp

lemma interior_crossPolytope_nonempty [Nonempty ι] : (interior (crossPolytope ι)).Nonempty :=
  ⟨0, mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset
    (Metric.closedBall_mem_nhds 0 (by positivity)) closedBall_subset_crossPolytope)⟩

/-- `N(cube, ε cube) ≤ (1 + 2/ε)^n` on `ι → ℝ`. -/
theorem translateCoveringNumber_supBall_smul_le {ε : ℝ} (hε : 0 < ε) :
    (translateCoveringNumber (supBall ι) (ε • supBall ι) : ℝ) ≤ (1 + 2 / ε) ^ Fintype.card ι := by
  have h := translateCoveringNumber_smul_self_le (E := ι → ℝ) convex_supBall neg_mem_supBall
    isBounded_supBall interior_supBall_nonempty hε
  rwa [Module.finrank_fintype_fun_eq_card] at h

/-- `N(Bₗ₁, ε Bₗ₁) ≤ (1 + 2/ε)^n` on `ι → ℝ`. -/
theorem translateCoveringNumber_crossPolytope_smul_le [Nonempty ι] {ε : ℝ} (hε : 0 < ε) :
    (translateCoveringNumber (crossPolytope ι) (ε • crossPolytope ι) : ℝ) ≤
      (1 + 2 / ε) ^ Fintype.card ι := by
  have h := translateCoveringNumber_smul_self_le (E := ι → ℝ) convex_crossPolytope
    neg_mem_crossPolytope isBounded_crossPolytope interior_crossPolytope_nonempty hε
  rwa [Module.finrank_fintype_fun_eq_card] at h

end Coordinates

end

end TheoremOS.Geometry
