import Mathlib
import Submission.Library.TheoremOS.InformationTheory.Entropy

/-!
# Perfect matchings of multigraphs and the perfect matching polytope

A loopless multigraph is given by two endpoint maps `left right : E → V` with `left e ≠ right e`.
A perfect matching is a set of edges `M` with exactly one edge of `M` at every vertex. Contents:
the counting identity `|S| = 2 #(edges of M inside S) + #(edges of M leaving S)`, hence
`|V| = 2 |M|`, `|V|` is even, and an odd set is left by at least one edge of every perfect
matching; the perfect matching polytope (convex hull of the indicator vectors) with the valid
equations and inequalities `0 ≤ y e ≤ 1`, `∑_{e ∋ v} y e = 1`, `∑ y = |V| / 2` and
`∑_{e ∈ δ(S)} y e ≥ 1` for odd `S`; the polytope as the set of edge marginals of probability laws
on perfect matchings; its extreme points are exactly the indicator vectors; faces cut out by tight
valid inequalities (odd cuts, edges) are extreme subsets; and the maximum entropy of a law on
perfect matchings with prescribed edge marginals: it is attained, lies in `[0, log #matchings]`,
vanishes at the vertices, and is concave on the polytope. The complete graph on `Fin n` with edges
`i < j` is `completeMultigraph n`; it has a perfect matching iff `n` is even.

Only the easy half of Edmonds' description is here: the inequalities are valid on the polytope.
The converse (they cut out the polytope) is not proved.

Sources: L. Lovász and M. D. Plummer, *Matching Theory*, North-Holland, 1986, Chapters 1 and 7;
A. Schrijver, *Combinatorial Optimization*, Springer, 2003, Chapters 18 and 25 (validity of the
degree and odd-cut constraints); G. M. Ziegler, *Lectures on Polytopes*, Springer, 1995,
Chapter 2 (faces); T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley,
2006, Chapter 2 (entropy). Textbook material; nothing here is specific to a benchmark problem.

Bridges: a statement with a structure `left right : E → V` + `loopless`, `Incident v e :=
left e = v ∨ right e = v`, `IsPerfectMatching M := ∀ v, ∃! e, e ∈ M ∧ Incident v e`, matchings as
the subtype with `Fintype.ofFinite`, `indicator`, `polytope := convexHull ℝ (range indicator)`,
`mean`, `feasibleLaws`, `Crosses`, `cut`, `degree` and `cutMass` written as here matches the
definitions below by `rfl` after building a `LooplessMultigraph` from its fields; a maximum
entropy `sSup (entropy '' feasibleLaws y)` with `entropy p := ∑ i, Real.negMulLog (p i)` is
`maxEntropy` by `rfl`. A perfect matching written as "exactly one edge at each vertex",
`(M.filter (incident to v)).card = 1`, is `isPerfectMatching_iff_card`; on pairs `i < j` of `Fin n`
written with `e.1.1 = v ∨ e.1.2 = v` it is `completeMultigraph_isPerfectMatching_iff`. For the
complete bipartite graph the polytope corresponds to the doubly stochastic matrices, where Mathlib
has `doublyStochastic_eq_convexHull_permMatrix` (that identification is not proved here).
-/

namespace TheoremOS.Combinatorics

open Finset Real

noncomputable section

/-- A multigraph without loops: every edge has two distinct endpoints. -/
structure LooplessMultigraph (V E : Type*) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

namespace LooplessMultigraph

variable {V E : Type*} (G : LooplessMultigraph V E)

/-- The edge `e` has `v` as an endpoint. -/
def Incident (v : V) (e : E) : Prop := G.left e = v ∨ G.right e = v

/-- The edge `e` has exactly one endpoint in `S`. -/
def Crosses (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

/-- The edge `e` has both endpoints in `S`. -/
def Inside (S : Finset V) (e : E) : Prop := G.left e ∈ S ∧ G.right e ∈ S

instance [DecidableEq V] (v : V) : DecidablePred (G.Incident v) := fun e =>
  inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

instance [DecidableEq V] (S : Finset V) : DecidablePred (G.Crosses S) := fun e =>
  inferInstanceAs (Decidable ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

instance [DecidableEq V] (S : Finset V) : DecidablePred (G.Inside S) := fun e =>
  inferInstanceAs (Decidable (G.left e ∈ S ∧ G.right e ∈ S))

/-- `M` is a perfect matching: every vertex lies on exactly one edge of `M`. -/
def IsPerfectMatching (M : Finset E) : Prop := ∀ v, ∃! e, e ∈ M ∧ G.Incident v e

theorem isPerfectMatching_iff_card [DecidableEq V] (M : Finset E) :
    G.IsPerfectMatching M ↔ ∀ v, #(M.filter (G.Incident v)) = 1 := by
  refine forall_congr' fun v => ?_
  rw [card_eq_one_iff_existsUnique]
  simp only [mem_filter]

/-! ## Counting -/

private lemma sum_ite_incident [DecidableEq V] (S : Finset V) (e : E) :
    (∑ v ∈ S, if G.Incident v e then 1 else 0 : ℕ) =
      2 * (if G.Inside S e then 1 else 0) + (if G.Crosses S e then 1 else 0) := by
  have hsplit : ∀ v, (if G.Incident v e then 1 else 0 : ℕ) =
      (if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0) := by
    intro v
    have := G.loopless e
    unfold Incident
    by_cases h1 : G.left e = v <;> by_cases h2 : G.right e = v <;> simp_all
  simp only [hsplit, sum_add_distrib, sum_ite_eq]
  unfold Inside Crosses
  by_cases h1 : G.left e ∈ S <;> by_cases h2 : G.right e ∈ S <;> simp [h1, h2]

/-- Double counting of the edges of `M` at the vertices of `S`. -/
theorem sum_card_filter_incident [DecidableEq V] (M : Finset E) (S : Finset V) :
    ∑ v ∈ S, #(M.filter (G.Incident v)) =
      2 * #(M.filter (G.Inside S)) + #(M.filter (G.Crosses S)) := by
  simp only [card_filter]
  rw [sum_comm, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun e _ => G.sum_ite_incident S e

variable {G}

namespace IsPerfectMatching

theorem card_filter_incident [DecidableEq V] {M : Finset E} (hM : G.IsPerfectMatching M) (v : V) :
    #(M.filter (G.Incident v)) = 1 :=
  (G.isPerfectMatching_iff_card M).1 hM v

/-- `|S| = 2 #(edges of M inside S) + #(edges of M leaving S)`. -/
theorem card_eq [DecidableEq V] {M : Finset E} (hM : G.IsPerfectMatching M) (S : Finset V) :
    #S = 2 * #(M.filter (G.Inside S)) + #(M.filter (G.Crosses S)) := by
  rw [← G.sum_card_filter_incident M S]
  simp [hM.card_filter_incident]

/-- A perfect matching has `|V| / 2` edges. -/
theorem card_univ_eq [Fintype V] {M : Finset E} (hM : G.IsPerfectMatching M) :
    Fintype.card V = 2 * #M := by
  classical
  have h := hM.card_eq univ
  have hin : M.filter (G.Inside univ) = M :=
    filter_true_of_mem fun e _ => ⟨mem_univ _, mem_univ _⟩
  have hcr : M.filter (G.Crosses univ) = ∅ :=
    filter_false_of_mem fun e _ h => by unfold Crosses at h; simp at h
  rw [hin, hcr, card_empty, add_zero, card_univ] at h
  exact h

theorem even_card [Fintype V] {M : Finset E} (hM : G.IsPerfectMatching M) :
    Even (Fintype.card V) :=
  ⟨#M, by rw [hM.card_univ_eq]; ring⟩

/-- An odd set of vertices is left by an odd number of edges of a perfect matching. -/
theorem odd_card_filter_crosses [DecidableEq V] {M : Finset E} (hM : G.IsPerfectMatching M)
    {S : Finset V} (hS : Odd #S) : Odd #(M.filter (G.Crosses S)) := by
  have h := hM.card_eq S
  obtain ⟨k, hk⟩ := hS
  exact ⟨k - #(M.filter (G.Inside S)), by omega⟩

/-- Every perfect matching has an edge leaving each odd set of vertices. -/
theorem one_le_card_filter_crosses [DecidableEq V] {M : Finset E} (hM : G.IsPerfectMatching M)
    {S : Finset V} (hS : Odd #S) : 1 ≤ #(M.filter (G.Crosses S)) :=
  (hM.odd_card_filter_crosses hS).pos

theorem card_eq_card [Fintype V] {M N : Finset E} (hM : G.IsPerfectMatching M)
    (hN : G.IsPerfectMatching N) : #M = #N := by
  have h1 := hM.card_univ_eq
  have h2 := hN.card_univ_eq
  omega

end IsPerfectMatching

end LooplessMultigraph

/-! ## Probability weights -/

/-- Nonnegative weights summing to one (the probability simplex). -/
def probabilityWeights (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

section Weights

variable {ι : Type*} [Fintype ι]

lemma mem_probabilityWeights_iff_isDistribution {p : ι → ℝ} :
    p ∈ probabilityWeights ι ↔ InformationTheory.IsDistribution p :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.nonneg, h.sum_eq_one⟩⟩

lemma convex_probabilityWeights : Convex ℝ (probabilityWeights ι) := by
  intro p hp q hq a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hp.2, hq.2,
      mul_one, hab]

lemma isCompact_probabilityWeights : IsCompact (probabilityWeights ι) := by
  have hbox : IsCompact (Set.univ.pi fun _ : ι => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset ?_ fun p hp => ?_
  · have h1 : IsClosed {p : ι → ℝ | ∀ i, 0 ≤ p i} := by
      rw [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed {p : ι → ℝ | ∑ i, p i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  · exact fun i _ => ⟨hp.1 i, (mem_probabilityWeights_iff_isDistribution.1 hp).le_one i⟩

lemma single_mem_probabilityWeights [DecidableEq ι] (i : ι) :
    Pi.single i 1 ∈ probabilityWeights ι := by
  refine ⟨fun j => ?_, by simp⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma continuous_entropy : Continuous (InformationTheory.entropy : (ι → ℝ) → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_negMulLog.comp (continuous_apply i)

/-- Entropy is concave on the probability simplex. -/
theorem concaveOn_entropy :
    ConcaveOn ℝ (probabilityWeights ι) (InformationTheory.entropy : (ι → ℝ) → ℝ) := by
  refine ⟨convex_probabilityWeights, fun p hp q hq a b ha hb hab => ?_⟩
  simp only [InformationTheory.entropy, smul_eq_mul, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  have := concaveOn_negMulLog.2 (Set.mem_Ici.2 (hp.1 i)) (Set.mem_Ici.2 (hq.1 i)) ha hb hab
  simpa only [smul_eq_mul, Pi.add_apply, Pi.smul_apply] using this

end Weights

private lemma eq_zero_of_mul_add_mul_eq_zero {a b s t : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (h : a * s + b * t = 0) : s = 0 ∧ t = 0 := by
  have h1 : a * s = 0 := by nlinarith [mul_nonneg ha.le hs, mul_nonneg hb.le ht]
  have h2 : b * t = 0 := by nlinarith [mul_nonneg ha.le hs, mul_nonneg hb.le ht]
  exact ⟨(mul_eq_zero.1 h1).resolve_left ha.ne', (mul_eq_zero.1 h2).resolve_left hb.ne'⟩

/-- The points of `A` where a valid linear inequality `c ≤ f` is tight form an extreme subset (a
face) of `A`. -/
theorem isExtreme_setOf_eq_of_le {F : Type*} [AddCommGroup F] [Module ℝ F] {A : Set F}
    {f : F → ℝ} (hf : IsLinearMap ℝ f) {c : ℝ} (hA : ∀ x ∈ A, c ≤ f x) :
    IsExtreme ℝ A {x | x ∈ A ∧ f x = c} := by
  refine ⟨fun x hx => hx.1, fun x₁ hx₁ x₂ hx₂ z hz hseg => ⟨hx₁, ?_⟩⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hc := hz.2
  rw [hf.map_add, hf.map_smul, hf.map_smul, smul_eq_mul, smul_eq_mul] at hc
  have key : a * (f x₁ - c) + b * (f x₂ - c) = 0 := by linear_combination hc - c * hab
  have := eq_zero_of_mul_add_mul_eq_zero ha hb (sub_nonneg.2 (hA x₁ hx₁)) (sub_nonneg.2 (hA x₂ hx₂))
    key
  linarith [this.1]

namespace LooplessMultigraph

variable {V E : Type*} (G : LooplessMultigraph V E)

/-- The perfect matchings of `G`. -/
abbrev Matching := {M : Finset E // G.IsPerfectMatching M}

instance matchingFintype [Finite E] : Fintype G.Matching := Fintype.ofFinite _

/-! ## The perfect matching polytope -/

private lemma isLinearMap_apply {E : Type*} (e : E) : IsLinearMap ℝ fun w : E → ℝ => w e :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

section Polytope

variable [DecidableEq E]

/-- The indicator vector of a perfect matching. -/
def indicator (M : G.Matching) (e : E) : ℝ := if e ∈ M.1 then 1 else 0

/-- The perfect matching polytope. -/
def polytope : Set (E → ℝ) := convexHull ℝ (Set.range G.indicator)

variable {G}

lemma indicator_nonneg (M : G.Matching) (e : E) : 0 ≤ G.indicator M e := by
  unfold indicator; split_ifs <;> norm_num

lemma indicator_le_one (M : G.Matching) (e : E) : G.indicator M e ≤ 1 := by
  unfold indicator; split_ifs <;> norm_num

lemma indicator_injective : Function.Injective G.indicator := by
  intro M N h
  apply Subtype.ext
  ext e
  have := congrFun h e
  unfold indicator at this
  by_cases h1 : e ∈ M.1 <;> by_cases h2 : e ∈ N.1 <;> simp_all

lemma indicator_mem_polytope (M : G.Matching) : G.indicator M ∈ G.polytope :=
  subset_convexHull ℝ _ ⟨M, rfl⟩

lemma convex_polytope : Convex ℝ G.polytope := convex_convexHull ℝ _

theorem polytope_nonempty_iff : G.polytope.Nonempty ↔ Nonempty G.Matching := by
  rw [polytope, convexHull_nonempty_iff, Set.range_nonempty_iff_nonempty]

/-- A linear inequality valid at every indicator vector is valid on the polytope. -/
theorem le_of_mem_polytope {f : (E → ℝ) → ℝ} (hf : IsLinearMap ℝ f) {c : ℝ}
    (h : ∀ M, c ≤ f (G.indicator M)) {y : E → ℝ} (hy : y ∈ G.polytope) : c ≤ f y := by
  have hsub : Set.range G.indicator ⊆ {w | c ≤ f w} := by
    rintro _ ⟨M, rfl⟩; exact h M
  exact convexHull_min hsub (convex_halfSpace_ge hf c) hy

theorem le_of_mem_polytope' {f : (E → ℝ) → ℝ} (hf : IsLinearMap ℝ f) {c : ℝ}
    (h : ∀ M, f (G.indicator M) ≤ c) {y : E → ℝ} (hy : y ∈ G.polytope) : f y ≤ c := by
  have hsub : Set.range G.indicator ⊆ {w | f w ≤ c} := by
    rintro _ ⟨M, rfl⟩; exact h M
  exact convexHull_min hsub (convex_halfSpace_le hf c) hy

theorem eq_of_mem_polytope {f : (E → ℝ) → ℝ} (hf : IsLinearMap ℝ f) {c : ℝ}
    (h : ∀ M, f (G.indicator M) = c) {y : E → ℝ} (hy : y ∈ G.polytope) : f y = c :=
  le_antisymm (le_of_mem_polytope' hf (fun M => (h M).le) hy)
    (le_of_mem_polytope hf (fun M => (h M).ge) hy)

theorem nonneg_of_mem_polytope {y : E → ℝ} (hy : y ∈ G.polytope) (e : E) : 0 ≤ y e :=
  le_of_mem_polytope (isLinearMap_apply e) (fun M => indicator_nonneg M e) hy

theorem le_one_of_mem_polytope {y : E → ℝ} (hy : y ∈ G.polytope) (e : E) : y e ≤ 1 :=
  le_of_mem_polytope' (isLinearMap_apply e) (fun M => indicator_le_one M e) hy

variable (G) [Fintype E]

/-- Edge marginals of weights on perfect matchings. -/
def mean (p : G.Matching → ℝ) (e : E) : ℝ := ∑ M, p M * G.indicator M e

/-- Probability laws on perfect matchings with edge marginals `y`. -/
def feasibleLaws (y : E → ℝ) : Set (G.Matching → ℝ) :=
  {p | p ∈ probabilityWeights G.Matching ∧ G.mean p = y}

/-- The largest entropy of a law on perfect matchings with edge marginals `y`. -/
def maxEntropy (y : E → ℝ) : ℝ := sSup (InformationTheory.entropy '' G.feasibleLaws y)

variable {G}

lemma isCompact_polytope : IsCompact G.polytope := by
  unfold polytope; exact (Set.finite_range _).isCompact_convexHull ℝ

lemma mean_single (M : G.Matching) : G.mean (Pi.single M 1) = G.indicator M := by
  ext e
  simp [mean, Pi.single_apply]

lemma isLinearMap_mean : IsLinearMap ℝ G.mean := by
  constructor
  · intro p q; ext e; simp [mean, add_mul, sum_add_distrib]
  · intro c p; ext e; simp [mean, mul_sum, mul_assoc]

lemma continuous_mean : Continuous G.mean :=
  continuous_pi fun _ => continuous_finsetSum _ fun M _ =>
    (continuous_apply M).mul continuous_const

/-- The polytope is the set of edge marginals of probability laws on perfect matchings. -/
theorem polytope_eq_image_mean : G.polytope = G.mean '' probabilityWeights G.Matching := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_probabilityWeights.is_linear_image isLinearMap_mean)
    rintro _ ⟨M, rfl⟩
    exact ⟨Pi.single M 1, single_mem_probabilityWeights M, mean_single M⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine mem_convexHull_of_exists_fintype p G.indicator hp.1 hp.2 (fun M => ⟨M, rfl⟩) ?_
    ext e
    simp [mean, Finset.sum_apply]

theorem mem_polytope_iff_nonempty_feasibleLaws {y : E → ℝ} :
    y ∈ G.polytope ↔ (G.feasibleLaws y).Nonempty := by
  rw [polytope_eq_image_mean]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h⟩⟩

end Polytope

/-! ## Valid equations and inequalities -/

section Constraints

variable [Fintype E] [DecidableEq E] [DecidableEq V]

/-- The total weight of the edges at `v`. -/
def degree (x : E → ℝ) (v : V) : ℝ := ∑ e, if G.Incident v e then x e else 0

/-- The edges with exactly one endpoint in `S`. -/
def cut (S : Finset V) : Finset E := univ.filter (G.Crosses S)

/-- The total weight of the edges leaving `S`. -/
def cutMass (x : E → ℝ) (S : Finset V) : ℝ := ∑ e ∈ G.cut S, x e

variable {G}

omit [DecidableEq E] in
lemma isLinearMap_degree (v : V) : IsLinearMap ℝ fun x : E → ℝ => G.degree x v := by
  constructor
  · intro x y
    simp only [degree, ← sum_add_distrib]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  · intro c x
    simp only [degree, smul_eq_mul, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    split_ifs <;> simp

omit [DecidableEq E] in
lemma isLinearMap_cutMass (S : Finset V) : IsLinearMap ℝ fun x : E → ℝ => G.cutMass x S :=
  ⟨fun x y => by simp [cutMass, sum_add_distrib], fun c x => by simp [cutMass, mul_sum]⟩

lemma degree_indicator (M : G.Matching) (v : V) : G.degree (G.indicator M) v = 1 := by
  have hset : univ.filter (fun e => G.Incident v e ∧ e ∈ M.1) = M.1.filter (G.Incident v) := by
    ext e; simp [and_comm]
  simp only [degree, indicator, ← ite_and]
  rw [sum_boole, hset, M.2.card_filter_incident v, Nat.cast_one]

lemma cutMass_indicator (M : G.Matching) (S : Finset V) :
    G.cutMass (G.indicator M) S = #(M.1.filter (G.Crosses S)) := by
  have hset : univ.filter (fun e => G.Crosses S e ∧ e ∈ M.1) = M.1.filter (G.Crosses S) := by
    ext e; simp [and_comm]
  simp only [cutMass, cut, indicator, sum_filter, ← ite_and]
  rw [sum_boole, hset]

/-- Every point of the polytope has weight `1` at each vertex. -/
theorem degree_eq_one_of_mem_polytope {y : E → ℝ} (hy : y ∈ G.polytope) (v : V) :
    G.degree y v = 1 :=
  eq_of_mem_polytope (isLinearMap_degree v) (fun M => degree_indicator M v) hy

/-- Every point of the polytope has weight at least `1` on the cut of an odd set. -/
theorem one_le_cutMass_of_mem_polytope {y : E → ℝ} (hy : y ∈ G.polytope) {S : Finset V}
    (hS : Odd #S) : 1 ≤ G.cutMass y S := by
  refine le_of_mem_polytope (isLinearMap_cutMass S) (fun M => ?_) hy
  show 1 ≤ G.cutMass (G.indicator M) S
  rw [cutMass_indicator]
  exact_mod_cast M.2.one_le_card_filter_crosses hS

/-- The points of the polytope where the cut of an odd set is tight form a face. -/
theorem isExtreme_oddCutFace {S : Finset V} (hS : Odd #S) :
    IsExtreme ℝ G.polytope {y | y ∈ G.polytope ∧ G.cutMass y S = 1} :=
  isExtreme_setOf_eq_of_le (isLinearMap_cutMass S)
    fun _ hy => one_le_cutMass_of_mem_polytope hy hS

omit [Fintype E] [DecidableEq V] in
/-- The points of the polytope vanishing on an edge form a face. -/
theorem isExtreme_edgeFace (e : E) :
    IsExtreme ℝ G.polytope {y | y ∈ G.polytope ∧ y e = 0} :=
  isExtreme_setOf_eq_of_le (isLinearMap_apply e) fun _ hy => nonneg_of_mem_polytope hy e

omit [DecidableEq V] in
lemma sum_indicator [Fintype V] (M : G.Matching) :
    ∑ e, G.indicator M e = (Fintype.card V : ℝ) / 2 := by
  simp only [indicator]
  rw [sum_boole, filter_univ_mem, M.2.card_univ_eq]
  push_cast
  ring

omit [DecidableEq V] in
/-- Every point of the polytope has total weight `|V| / 2`. -/
theorem sum_eq_of_mem_polytope [Fintype V] {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∑ e, y e = (Fintype.card V : ℝ) / 2 :=
  eq_of_mem_polytope (f := fun x : E → ℝ => ∑ e, x e)
    ⟨fun x y => by simp [sum_add_distrib], fun c x => by simp [mul_sum]⟩ sum_indicator hy

omit [Fintype E] [DecidableEq V] in
/-- The indicator vectors are extreme points of the polytope. -/
theorem indicator_mem_extremePoints (M : G.Matching) :
    G.indicator M ∈ G.polytope.extremePoints ℝ := by
  rw [mem_extremePoints]
  refine ⟨indicator_mem_polytope M, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, he⟩ := hseg
  have hpt : ∀ e, x₁ e = G.indicator M e ∧ x₂ e = G.indicator M e := by
    intro e
    have h := congrFun he e
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
    unfold indicator at h ⊢
    split_ifs at h ⊢
    · have key : a * (1 - x₁ e) + b * (1 - x₂ e) = 0 := by linear_combination hab - h
      have := eq_zero_of_mul_add_mul_eq_zero ha hb (sub_nonneg.2 (le_one_of_mem_polytope hx₁ e))
        (sub_nonneg.2 (le_one_of_mem_polytope hx₂ e)) key
      constructor <;> linarith [this.1, this.2]
    · exact eq_zero_of_mul_add_mul_eq_zero ha hb (nonneg_of_mem_polytope hx₁ e)
        (nonneg_of_mem_polytope hx₂ e) h
  exact ⟨funext fun e => (hpt e).1, funext fun e => (hpt e).2⟩

omit [Fintype E] [DecidableEq V] in
/-- The extreme points of the perfect matching polytope are exactly the indicator vectors. -/
theorem extremePoints_polytope : G.polytope.extremePoints ℝ = Set.range G.indicator :=
  Set.Subset.antisymm extremePoints_convexHull_subset
    (by rintro _ ⟨M, rfl⟩; exact indicator_mem_extremePoints M)

end Constraints

/-! ## Maximum entropy with prescribed edge marginals -/

section MaxEntropy

variable [Fintype E] [DecidableEq E]

lemma feasibleLaws_eq (y : E → ℝ) :
    G.feasibleLaws y = probabilityWeights G.Matching ∩ G.mean ⁻¹' {y} := rfl

lemma convex_feasibleLaws (y : E → ℝ) : Convex ℝ (G.feasibleLaws y) := by
  intro p hp q hq a b ha hb hab
  refine ⟨convex_probabilityWeights hp.1 hq.1 ha hb hab, ?_⟩
  rw [isLinearMap_mean.map_add, isLinearMap_mean.map_smul, isLinearMap_mean.map_smul, hp.2, hq.2,
    ← add_smul, hab, one_smul]

lemma isCompact_feasibleLaws (y : E → ℝ) : IsCompact (G.feasibleLaws y) := by
  rw [feasibleLaws_eq]
  exact isCompact_probabilityWeights.inter_right (isClosed_singleton.preimage continuous_mean)

lemma bddAbove_entropy_image (y : E → ℝ) :
    BddAbove (InformationTheory.entropy '' G.feasibleLaws y) := by
  refine ⟨log (Fintype.card G.Matching), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact InformationTheory.entropy_le_log_card (mem_probabilityWeights_iff_isDistribution.1 hp.1)

lemma maxEntropy_nonneg (y : E → ℝ) : 0 ≤ G.maxEntropy y := by
  apply Real.sSup_nonneg
  rintro _ ⟨p, hp, rfl⟩
  exact InformationTheory.entropy_nonneg (mem_probabilityWeights_iff_isDistribution.1 hp.1)

/-- `maxEntropy y ≤ log (number of perfect matchings)`. -/
lemma maxEntropy_le_log_card (y : E → ℝ) : G.maxEntropy y ≤ log (Fintype.card G.Matching) := by
  rcases (G.feasibleLaws y).eq_empty_or_nonempty with h | h
  · rw [maxEntropy, h, Set.image_empty, Real.sSup_empty]
    exact log_natCast_nonneg _
  · refine csSup_le (h.image _) ?_
    rintro _ ⟨p, hp, rfl⟩
    exact InformationTheory.entropy_le_log_card (mem_probabilityWeights_iff_isDistribution.1 hp.1)

variable {G}

lemma le_maxEntropy {y : E → ℝ} {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y) :
    InformationTheory.entropy p ≤ G.maxEntropy y :=
  le_csSup (bddAbove_entropy_image G y) ⟨p, hp, rfl⟩

lemma maxEntropy_of_notMem_polytope {y : E → ℝ} (hy : y ∉ G.polytope) : G.maxEntropy y = 0 := by
  rw [mem_polytope_iff_nonempty_feasibleLaws, Set.not_nonempty_iff_eq_empty] at hy
  rw [maxEntropy, hy, Set.image_empty, Real.sSup_empty]

/-- On the polytope the maximum entropy is attained. -/
theorem exists_maxEntropy {y : E → ℝ} (hy : y ∈ G.polytope) :
    ∃ p ∈ G.feasibleLaws y, InformationTheory.entropy p = G.maxEntropy y := by
  have hne := mem_polytope_iff_nonempty_feasibleLaws.1 hy
  have hK : IsCompact (InformationTheory.entropy '' G.feasibleLaws y) :=
    (isCompact_feasibleLaws G y).image continuous_entropy
  exact hK.sSup_mem (hne.image _)

/-- At a vertex of the polytope the only feasible law is the point mass. -/
theorem feasibleLaws_indicator [Fintype V] (M : G.Matching) :
    G.feasibleLaws (G.indicator M) = {Pi.single M 1} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨single_mem_probabilityWeights M, mean_single M⟩, ?_⟩
  rintro p ⟨hp, hmean⟩
  have hzero : ∀ N, N ≠ M → p N = 0 := by
    intro N hNM
    have hns : ¬ N.1 ⊆ M.1 := fun hsub => hNM (Subtype.ext
      (eq_of_subset_of_card_le hsub (M.2.card_eq_card N.2).le))
    obtain ⟨e, heN, heM⟩ := not_subset.1 hns
    have h := congrFun hmean e
    have hM0 : G.indicator M e = 0 := by simp [indicator, heM]
    rw [hM0, mean] at h
    have hterm := (sum_eq_zero_iff_of_nonneg fun K _ =>
      mul_nonneg (hp.1 K) (indicator_nonneg K e)).1 h N (mem_univ N)
    simpa [indicator, heN] using hterm
  funext N
  by_cases hN : N = M
  · rw [hN, Pi.single_eq_same]
    have hsum := hp.2
    rw [sum_eq_single M (fun K _ hK => hzero K hK) (by simp)] at hsum
    exact hsum
  · rw [Pi.single_eq_of_ne hN]
    exact hzero N hN

/-- The maximum entropy vanishes at the vertices of the polytope. -/
theorem maxEntropy_indicator [Fintype V] (M : G.Matching) : G.maxEntropy (G.indicator M) = 0 := by
  rw [maxEntropy, feasibleLaws_indicator, Set.image_singleton, csSup_singleton,
    InformationTheory.entropy]
  refine sum_eq_zero fun N _ => ?_
  by_cases hN : N = M
  · rw [hN, Pi.single_eq_same, negMulLog_one]
  · rw [Pi.single_eq_of_ne hN, negMulLog_zero]

variable (G) in
/-- The maximum entropy is concave on the polytope. -/
theorem concaveOn_maxEntropy : ConcaveOn ℝ G.polytope G.maxEntropy := by
  refine ⟨convex_polytope, fun y hy z hz a b ha hb hab => ?_⟩
  obtain ⟨p, hp, hpH⟩ := exists_maxEntropy hy
  obtain ⟨q, hq, hqH⟩ := exists_maxEntropy hz
  have hr : a • p + b • q ∈ G.feasibleLaws (a • y + b • z) := by
    refine ⟨convex_probabilityWeights hp.1 hq.1 ha hb hab, ?_⟩
    rw [isLinearMap_mean.map_add, isLinearMap_mean.map_smul, isLinearMap_mean.map_smul, hp.2, hq.2]
  calc a • G.maxEntropy y + b • G.maxEntropy z
      = a • InformationTheory.entropy p + b • InformationTheory.entropy q := by rw [hpH, hqH]
    _ ≤ InformationTheory.entropy (a • p + b • q) := concaveOn_entropy.2 hp.1 hq.1 ha hb hab
    _ ≤ G.maxEntropy (a • y + b • z) := le_maxEntropy hr

end MaxEntropy

end LooplessMultigraph

/-! ## The complete graph -/

/-- The edges `(i, j)`, `i < j`, of the complete graph on `Fin n`. -/
abbrev CompleteEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The complete graph on `Fin n`. -/
def completeMultigraph (n : ℕ) : LooplessMultigraph (Fin n) (CompleteEdge n) where
  left e := e.1.1
  right e := e.1.2
  loopless e := e.2.ne

/-- In the complete graph, a perfect matching is a set of pairs `i < j` touching every vertex
exactly once. -/
theorem completeMultigraph_isPerfectMatching_iff {n : ℕ} (M : Finset (CompleteEdge n)) :
    (completeMultigraph n).IsPerfectMatching M ↔
      ∀ v, #(M.filter fun e => e.1.1 = v ∨ e.1.2 = v) = 1 :=
  (completeMultigraph n).isPerfectMatching_iff_card M

/-- Every perfect matching of the complete graph has a pair with exactly one end in each odd set. -/
theorem completeMultigraph_one_le_card_filter_crosses {n : ℕ} {M : Finset (CompleteEdge n)}
    (hM : (completeMultigraph n).IsPerfectMatching M) {S : Finset (Fin n)} (hS : Odd #S) :
    1 ≤ #(M.filter fun e => (e.1.1 ∈ S ∧ e.1.2 ∉ S) ∨ (e.1.1 ∉ S ∧ e.1.2 ∈ S)) :=
  hM.one_le_card_filter_crosses hS

/-- The pairs `(2i, 2i + 1)`. -/
def standardMatching (n : ℕ) : Finset (CompleteEdge n) :=
  univ.filter fun e => e.1.1.1 % 2 = 0 ∧ e.1.2.1 = e.1.1.1 + 1

/-- For even `n` the pairs `(2i, 2i + 1)` form a perfect matching of the complete graph. -/
theorem standardMatching_isPerfectMatching {n : ℕ} (hn : Even n) :
    (completeMultigraph n).IsPerfectMatching (standardMatching n) := by
  intro v
  obtain ⟨k, hk⟩ := hn
  have hv := v.2
  have h1 : v.1 - v.1 % 2 < n := by omega
  have h2 : v.1 - v.1 % 2 + 1 < n := by omega
  refine ⟨⟨(⟨_, h1⟩, ⟨_, h2⟩), Fin.mk_lt_mk.2 (Nat.lt_succ_self _)⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [standardMatching, mem_filter, mem_univ, true_and, and_true]; omega
  · simp only [LooplessMultigraph.Incident, completeMultigraph, Fin.ext_iff]; omega
  · rintro ⟨⟨x, y⟩, hxy⟩ ⟨he, hinc⟩
    simp only [standardMatching, mem_filter, mem_univ, true_and] at he
    simp only [LooplessMultigraph.Incident, completeMultigraph, Fin.ext_iff] at hinc
    apply Subtype.ext
    simp only [Prod.mk.injEq, Fin.ext_iff]
    omega

/-- The complete graph on `Fin n` has a perfect matching iff `n` is even. -/
theorem completeMultigraph_nonempty_matching_iff {n : ℕ} :
    Nonempty (completeMultigraph n).Matching ↔ Even n := by
  constructor
  · rintro ⟨M⟩
    simpa using M.2.even_card
  · intro hn
    exact ⟨⟨_, standardMatching_isPerfectMatching hn⟩⟩

end

end TheoremOS.Combinatorics
