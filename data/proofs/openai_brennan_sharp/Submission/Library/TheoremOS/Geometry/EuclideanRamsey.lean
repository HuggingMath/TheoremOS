import Mathlib

/-!
# Euclidean Ramsey configurations: basic theory

A configuration `a : ι → P` is *Ramsey* (`IsEuclideanRamsey a`) when for every `r ≥ 2` some
`ℝ^D`, `D ≥ 1`, has a monochromatic congruent copy of `a` in every `r`-colouring
(`MonoCopies a D r`). This file proves: congruent copies form an equivalence and are preserved by
isometries; Ramsey transfers along congruence, reindexing and sub-configurations; monotonicity in
the number of colours and in the dimension (zero padding `padZero` is an isometry); every
equilateral configuration, in particular every configuration with at most two distinct points, is
Ramsey; compactness (a finite set of points already forces a monochromatic copy); and the product
theorem: if `a` and `a'` are Ramsey and `p` has `dist (p x) (p y)² = dist (a x.1) (a y.1)² +
dist (a' x.2) (a' y.2)²`, then `p` is Ramsey (`euclideanJoin` realises such products in
`ℝ^(d + d')`).

Sources: P. Erdős, R. L. Graham, P. Montgomery, B. L. Rothschild, J. Spencer and E. G. Straus,
*Euclidean Ramsey theorems I*, J. Combin. Theory Ser. A 14 (1973) 341–363 (the definition, the
compactness argument, products of Ramsey sets, simplices with equal edges via pigeonhole);
R. L. Graham, *Euclidean Ramsey theory*, in *Handbook of Discrete and Computational Geometry*
(J. E. Goodman and J. O'Rourke, eds.) (survey of these facts). Classical material; nothing here is
specific to a benchmark problem.

Bridges: with `Space d := EuclideanSpace ℝ (Fin d)` and
`Congruent a b := ∀ i j, dist (b i) (b j) = dist (a i) (a j)`, a definition
`Ramsey a := ∀ r, 2 ≤ r → ∃ D, 1 ≤ D ∧ ∀ c : Space D → Fin r, ∃ b, Congruent a b ∧ ∃ k, ∀ i,
c (b i) = k` is `IsEuclideanRamsey a` by `Iff.rfl`, and `Congruent a b` is `CongruentCopy a b`.
Products indexed by `Fin s × Fin t` move to `Fin (s * t)` with `IsEuclideanRamsey.comp_equiv`
and `finProdFinEquiv`.
-/

namespace TheoremOS.Geometry

open Set Function

noncomputable section

/-- `b` is a congruent copy of `a`: all pairwise distances agree. -/
def CongruentCopy {ι P Q : Type*} [Dist P] [Dist Q] (a : ι → P) (b : ι → Q) : Prop :=
  ∀ i j, dist (b i) (b j) = dist (a i) (a j)

/-- Every `r`-colouring of `ℝ^D` has a monochromatic congruent copy of `a`. -/
def MonoCopies {ι P : Type*} [Dist P] (a : ι → P) (D r : ℕ) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin D) → Fin r, ∃ b : ι → EuclideanSpace ℝ (Fin D),
    CongruentCopy a b ∧ ∃ k : Fin r, ∀ i, c (b i) = k

/-- `a` is Ramsey: for every `r ≥ 2` some `ℝ^D` with `D ≥ 1` has `MonoCopies a D r`. -/
def IsEuclideanRamsey {ι P : Type*} [Dist P] (a : ι → P) : Prop :=
  ∀ r : ℕ, 2 ≤ r → ∃ D : ℕ, 1 ≤ D ∧ MonoCopies a D r

variable {ι κ P Q R : Type*}

section Congruent

variable [PseudoMetricSpace P] [PseudoMetricSpace Q] [PseudoMetricSpace R]

theorem CongruentCopy.refl (a : ι → P) : CongruentCopy a a := fun _ _ => rfl

theorem CongruentCopy.symm {a : ι → P} {b : ι → Q} (h : CongruentCopy a b) : CongruentCopy b a :=
  fun i j => (h i j).symm

theorem CongruentCopy.trans {a : ι → P} {b : ι → Q} {c : ι → R} (hab : CongruentCopy a b)
    (hbc : CongruentCopy b c) : CongruentCopy a c := fun i j => (hbc i j).trans (hab i j)

theorem CongruentCopy.comp {a : ι → P} {b : ι → Q} (h : CongruentCopy a b) (f : κ → ι) :
    CongruentCopy (a ∘ f) (b ∘ f) := fun i j => h (f i) (f j)

theorem congruentCopy_comp_isometry (a : ι → P) {g : P → Q} (hg : Isometry g) :
    CongruentCopy a (g ∘ a) := fun i j => hg.dist_eq (a i) (a j)

theorem CongruentCopy.comp_isometry {a : ι → P} {b : ι → Q} (h : CongruentCopy a b) {g : Q → R}
    (hg : Isometry g) : CongruentCopy a (g ∘ b) := h.trans (congruentCopy_comp_isometry b hg)

end Congruent

section Transfer

variable [PseudoMetricSpace P] [PseudoMetricSpace Q]

theorem MonoCopies.of_congruentCopy {a : ι → P} {a' : ι → Q} (h : CongruentCopy a a') {D r : ℕ}
    (ha : MonoCopies a D r) : MonoCopies a' D r := fun c => by
  obtain ⟨b, hb, k, hk⟩ := ha c
  exact ⟨b, h.symm.trans hb, k, hk⟩

theorem IsEuclideanRamsey.of_congruentCopy {a : ι → P} {a' : ι → Q} (h : CongruentCopy a a')
    (ha : IsEuclideanRamsey a) : IsEuclideanRamsey a' := fun r hr => by
  obtain ⟨D, hD, hm⟩ := ha r hr
  exact ⟨D, hD, hm.of_congruentCopy h⟩

theorem isEuclideanRamsey_congr {a : ι → P} {a' : ι → Q} (h : CongruentCopy a a') :
    IsEuclideanRamsey a ↔ IsEuclideanRamsey a' :=
  ⟨IsEuclideanRamsey.of_congruentCopy h, IsEuclideanRamsey.of_congruentCopy h.symm⟩

theorem MonoCopies.comp {a : ι → P} {D r : ℕ} (ha : MonoCopies a D r) (f : κ → ι) :
    MonoCopies (a ∘ f) D r := fun c => by
  obtain ⟨b, hb, k, hk⟩ := ha c
  exact ⟨b ∘ f, hb.comp f, k, fun i => hk (f i)⟩

/-- Reindexed configurations of a Ramsey configuration are Ramsey. -/
theorem IsEuclideanRamsey.comp {a : ι → P} (ha : IsEuclideanRamsey a) (f : κ → ι) :
    IsEuclideanRamsey (a ∘ f) := fun r hr => by
  obtain ⟨D, hD, hm⟩ := ha r hr
  exact ⟨D, hD, hm.comp f⟩

theorem IsEuclideanRamsey.comp_equiv {a : ι → P} (e : κ ≃ ι) :
    IsEuclideanRamsey (a ∘ e) ↔ IsEuclideanRamsey a :=
  ⟨fun h => by simpa [comp_def] using h.comp e.symm, fun h => h.comp e⟩

/-- Sub-configurations of Ramsey configurations are Ramsey. -/
theorem IsEuclideanRamsey.of_range_subset {a : ι → P} (ha : IsEuclideanRamsey a) {a' : κ → P}
    (h : range a' ⊆ range a) : IsEuclideanRamsey a' := by
  choose f hf using fun j => h (mem_range_self (f := a') j)
  have : a' = a ∘ f := funext fun j => (hf j).symm
  rw [this]
  exact ha.comp f

/-- Fewer colours: `MonoCopies a D r → MonoCopies a D r'` for `r' ≤ r`. -/
theorem MonoCopies.mono_colours {a : ι → P} {D r r' : ℕ} (ha : MonoCopies a D r) (h : r' ≤ r) :
    MonoCopies a D r' := fun c => by
  obtain ⟨b, hb, k, hk⟩ := ha (Fin.castLE h ∘ c)
  refine ⟨b, hb, ?_⟩
  by_cases hι : IsEmpty ι
  · obtain ⟨x⟩ : Nonempty (EuclideanSpace ℝ (Fin D)) := inferInstance
    exact ⟨c x, fun i => isEmptyElim i⟩
  · obtain ⟨i₀⟩ := not_isEmpty_iff.mp hι
    refine ⟨c (b i₀), fun i => Fin.castLE_injective h ?_⟩
    exact (hk i).trans (hk i₀).symm

end Transfer

section Dimension

/-- Zero padding `ℝ^D → ℝ^E` for `D ≤ E`. -/
def padZero {D E : ℕ} (_h : D ≤ E) (x : EuclideanSpace ℝ (Fin D)) : EuclideanSpace ℝ (Fin E) :=
  WithLp.toLp 2 fun j => if hj : (j : ℕ) < D then x ⟨j, hj⟩ else 0

theorem isometry_padZero {D E : ℕ} (h : D ≤ E) : Isometry (padZero h) := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  congr 1
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro j hj
    have hjD : ¬ (j : ℕ) < D := fun hlt => hj ⟨⟨j, hlt⟩, Fin.ext rfl⟩
    simp [padZero, hjD]
  · intro i
    simp [padZero, i.isLt]

theorem MonoCopies.mono_dim [PseudoMetricSpace P] {a : ι → P} {D E r : ℕ} (ha : MonoCopies a D r)
    (h : D ≤ E) : MonoCopies a E r := fun c => by
  obtain ⟨b, hb, k, hk⟩ := ha (c ∘ padZero h)
  exact ⟨padZero h ∘ b, hb.comp_isometry (isometry_padZero h), k, hk⟩

theorem IsEuclideanRamsey.eventually [PseudoMetricSpace P] {a : ι → P} (ha : IsEuclideanRamsey a)
    {r : ℕ} (hr : 2 ≤ r) : ∃ D₀, ∀ D, D₀ ≤ D → MonoCopies a D r := by
  obtain ⟨D₀, -, h⟩ := ha r hr
  exact ⟨D₀, fun D hD => h.mono_dim hD⟩

/-- Ramsey means: for every `r ≥ 2`, all large enough dimensions work. -/
theorem isEuclideanRamsey_iff_eventually [PseudoMetricSpace P] {a : ι → P} :
    IsEuclideanRamsey a ↔ ∀ r : ℕ, 2 ≤ r → ∃ D₀, ∀ D, D₀ ≤ D → MonoCopies a D r :=
  ⟨fun ha _ hr => ha.eventually hr, fun h r hr => by
    obtain ⟨D₀, hD⟩ := h r hr
    exact ⟨max D₀ 1, le_max_right _ _, hD _ (le_max_left _ _)⟩⟩

end Dimension

section Equilateral

lemma dist_single_single_of_ne {D : ℕ} {m m' : Fin D} (hmm : m ≠ m') (t : ℝ) :
    dist (EuclideanSpace.single m t) (EuclideanSpace.single m' t) = √2 * |t| := by
  rw [dist_eq_norm]
  have hsq : ‖EuclideanSpace.single m t - EuclideanSpace.single m' t‖ ^ 2 = (√2 * |t|) ^ 2 := by
    rw [@norm_sub_sq_real, PiLp.norm_single, PiLp.norm_single,
      EuclideanSpace.inner_single_left]
    simp [hmm, mul_pow]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Equilateral configurations are Ramsey** (pigeonhole on the vertices of a regular simplex
with `r · |ι| + 1` vertices). -/
theorem isEuclideanRamsey_of_equilateral [Finite ι] [PseudoMetricSpace P] {a : ι → P} {δ : ℝ}
    (hδ : 0 ≤ δ) (h : ∀ i j, i ≠ j → dist (a i) (a j) = δ) : IsEuclideanRamsey a := by
  classical
  have := Fintype.ofFinite ι
  intro r _
  refine ⟨r * Fintype.card ι + 1, by omega, fun c => ?_⟩
  let v : Fin (r * Fintype.card ι + 1) → EuclideanSpace ℝ (Fin (r * Fintype.card ι + 1)) :=
    fun m => EuclideanSpace.single m (δ / √2)
  have hv : ∀ m m', m ≠ m' → dist (v m) (v m') = δ := by
    intro m m' hmm
    have h2 : (0 : ℝ) < √2 := by positivity
    rw [dist_single_single_of_ne hmm, abs_of_nonneg (div_nonneg hδ h2.le)]
    field_simp
  obtain ⟨k, hk⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := fun m => c (v m))
    (n := Fintype.card ι) (by rw [Fintype.card_fin, Fintype.card_fin]; omega)
  set F := Finset.univ.filter fun m => c (v m) = k
  have hcard : Fintype.card ι ≤ F.card := hk.le
  let g : ι → Fin (r * Fintype.card ι + 1) := fun i =>
    F.orderEmbOfFin rfl (Fin.castLE hcard (Fintype.equivFin ι i))
  have hg : Injective g := fun i j hij =>
    (Fintype.equivFin ι).injective (Fin.castLE_injective hcard ((F.orderEmbOfFin rfl).injective hij))
  have hgF : ∀ i, g i ∈ F := fun i => F.orderEmbOfFin_mem rfl _
  refine ⟨fun i => v (g i), fun i j => ?_, k, fun i => (Finset.mem_filter.mp (hgF i)).2⟩
  by_cases hij : i = j
  · subst hij; simp
  · rw [hv _ _ (hg.ne hij), h i j hij]

/-- Two-point configurations are Ramsey. -/
theorem isEuclideanRamsey_pair [PseudoMetricSpace P] (x y : P) : IsEuclideanRamsey ![x, y] :=
  isEuclideanRamsey_of_equilateral (δ := dist x y) dist_nonneg fun i j hij => by
    fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- Configurations with at most two distinct points are Ramsey. -/
theorem isEuclideanRamsey_of_range_subset_pair [PseudoMetricSpace P] {a : ι → P} {x y : P}
    (h : range a ⊆ {x, y}) : IsEuclideanRamsey a :=
  (isEuclideanRamsey_pair x y).of_range_subset fun z hz => by
    rcases Set.mem_insert_iff.mp (h hz) with hzx | hzy
    · exact ⟨0, hzx.symm⟩
    · exact ⟨1, (Set.mem_singleton_iff.mp hzy).symm⟩

theorem isEuclideanRamsey_of_subsingleton [Subsingleton ι] [PseudoMetricSpace P] (a : ι → P) :
    IsEuclideanRamsey a :=
  isEuclideanRamsey_of_equilateral le_rfl fun i j hij => absurd (Subsingleton.elim i j) hij

end Equilateral

section Compactness

/-- **Compactness**: if every `r`-colouring of `ℝ^D` has a monochromatic copy of a finite
configuration, then a finite set `X` of points already contains one for every colouring. -/
theorem MonoCopies.exists_finset [Finite ι] [PseudoMetricSpace P] {a : ι → P} {D r : ℕ}
    (ha : MonoCopies a D r) :
    ∃ X : Finset (EuclideanSpace ℝ (Fin D)), ∀ c : EuclideanSpace ℝ (Fin D) → Fin r,
      ∃ b : ι → EuclideanSpace ℝ (Fin D), (∀ i, b i ∈ X) ∧ CongruentCopy a b ∧
        ∃ k : Fin r, ∀ i, c (b i) = k := by
  classical
  have := Fintype.ofFinite ι
  by_contra hne
  push Not at hne
  let K : Finset (EuclideanSpace ℝ (Fin D)) → Set (EuclideanSpace ℝ (Fin D) → Fin r) := fun X =>
    {c | ∀ b : ι → EuclideanSpace ℝ (Fin D), (∀ i, b i ∈ X) → CongruentCopy a b →
      ∀ k : Fin r, ∃ i, c (b i) ≠ k}
  have hcl : ∀ X, IsClosed (K X) := by
    intro X
    have e : K X = ⋂ (b : ι → EuclideanSpace ℝ (Fin D)) (_ : ∀ i, b i ∈ X) (_ : CongruentCopy a b),
        {c : EuclideanSpace ℝ (Fin D) → Fin r | ∀ k : Fin r, ∃ i, c (b i) ≠ k} := by
      ext c; simp only [K, Set.mem_iInter, Set.mem_ofPred_eq]
    rw [e]
    refine isClosed_iInter fun b => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    have hcont : Continuous fun c : EuclideanSpace ℝ (Fin D) → Fin r => fun i => c (b i) :=
      continuous_pi fun i => continuous_apply (b i)
    exact (isClosed_discrete {f : ι → Fin r | ∀ k : Fin r, ∃ i, f i ≠ k}).preimage hcont
  have hdir : Directed (· ⊇ ·) K := fun X Y => ⟨X ∪ Y,
    fun _ hc b hb => hc b fun i => Finset.mem_union_left _ (hb i),
    fun _ hc b hb => hc b fun i => Finset.mem_union_right _ (hb i)⟩
  have hnon : ∀ X, (K X).Nonempty := fun X => by
    obtain ⟨c, hc⟩ := hne X
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir hnon
    (fun X => (hcl X).isCompact) hcl
  obtain ⟨b, hb, k, hk⟩ := ha c
  rw [Set.mem_iInter] at hc
  obtain ⟨i, hi⟩ := hc (Finset.univ.image b) b
    (fun i => Finset.mem_image_of_mem b (Finset.mem_univ i)) hb k
  exact hi (hk i)

end Compactness

section Product

/-- `ℝ^d × ℝ^d' → ℝ^(d + d')`, concatenating coordinates. -/
def euclideanJoin {d d' : ℕ} (x : EuclideanSpace ℝ (Fin d)) (y : EuclideanSpace ℝ (Fin d')) :
    EuclideanSpace ℝ (Fin (d + d')) :=
  WithLp.toLp 2 (Fin.append (WithLp.ofLp x) (WithLp.ofLp y))

theorem dist_euclideanJoin_sq {d d' : ℕ} (x x' : EuclideanSpace ℝ (Fin d))
    (y y' : EuclideanSpace ℝ (Fin d')) :
    dist (euclideanJoin x y) (euclideanJoin x' y') ^ 2 = dist x x' ^ 2 + dist y y' ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
    Fin.sum_univ_add]
  simp [euclideanJoin]

/-- **Products of Ramsey configurations are Ramsey.** If `a` and `a'` are Ramsey and
`dist (p x) (p y)² = dist (a x.1) (a y.1)² + dist (a' x.2) (a' y.2)²` (as for
`p x = euclideanJoin (a x.1) (a' x.2)`), then `p` is Ramsey. -/
theorem IsEuclideanRamsey.prod [Finite ι] [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [PseudoMetricSpace R] {a : ι → P} {a' : κ → Q} (ha : IsEuclideanRamsey a)
    (ha' : IsEuclideanRamsey a') {p : ι × κ → R}
    (hp : ∀ x y, dist (p x) (p y) ^ 2 = dist (a x.1) (a y.1) ^ 2 + dist (a' x.2) (a' y.2) ^ 2) :
    IsEuclideanRamsey p := by
  classical
  intro r hr
  obtain ⟨D₁, hD₁, h₁⟩ := ha r hr
  obtain ⟨X, hX⟩ := h₁.exists_finset
  -- Colour `ℝ^D₂` by the colour pattern each point induces on the finite set `X`.
  obtain ⟨N, hN, hN2⟩ : ∃ N, Fintype.card (X → Fin r) < N ∧ 2 ≤ N :=
    ⟨Fintype.card (X → Fin r) + 2, by omega, by omega⟩
  let enc : (X → Fin r) → Fin N := fun f => Fin.castLE hN.le (Fintype.equivFin _ f)
  have henc : Injective enc := fun f g h =>
    (Fintype.equivFin _).injective (Fin.castLE_injective hN.le h)
  obtain ⟨D₂, hD₂, h₂⟩ := ha' N hN2
  refine ⟨D₁ + D₂, by omega, fun c => ?_⟩
  obtain ⟨b₂, hb₂, k₂, hk₂⟩ :=
    h₂ fun y => enc fun x => c (euclideanJoin (x : EuclideanSpace ℝ (Fin D₁)) y)
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨l₀⟩⟩
  · exact ⟨fun x => isEmptyElim x.2, fun x => isEmptyElim x.2, ⟨0, by omega⟩,
      fun x => isEmptyElim x.2⟩
  have hpat : ∀ l, (fun x : X => c (euclideanJoin (x : EuclideanSpace ℝ (Fin D₁)) (b₂ l))) =
      fun x : X => c (euclideanJoin (x : EuclideanSpace ℝ (Fin D₁)) (b₂ l₀)) :=
    fun l => henc ((hk₂ l).trans (hk₂ l₀).symm)
  obtain ⟨b₁, hb₁X, hb₁, k₁, hk₁⟩ := hX fun z => c (euclideanJoin z (b₂ l₀))
  refine ⟨fun x => euclideanJoin (b₁ x.1) (b₂ x.2), fun x y => ?_, k₁, fun x => ?_⟩
  · refine (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp ?_
    rw [dist_euclideanJoin_sq, hb₁, hb₂, hp]
  · have := congrFun (hpat x.2) ⟨b₁ x.1, hb₁X x.1⟩
    simp only at this ⊢
    rw [this]
    exact hk₁ x.1

theorem IsEuclideanRamsey.join [Finite ι] {d d' : ℕ} {a : ι → EuclideanSpace ℝ (Fin d)}
    {a' : κ → EuclideanSpace ℝ (Fin d')} (ha : IsEuclideanRamsey a) (ha' : IsEuclideanRamsey a') :
    IsEuclideanRamsey fun x : ι × κ => euclideanJoin (a x.1) (a' x.2) :=
  ha.prod ha' fun _ _ => dist_euclideanJoin_sq _ _ _ _

end Product

end

end TheoremOS.Geometry
