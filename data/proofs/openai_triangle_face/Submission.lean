import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uIndex uι

namespace MatchingEntropyBounds

structure LooplessGraph (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

variable {V : Type uV} {E : Type uE}
  [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

namespace LooplessGraph

def Incident (G : LooplessGraph V E) (v : V) (e : E) : Prop :=
  G.left e = v ∨ G.right e = v

instance incidentDecidable (G : LooplessGraph V E) (v : V) (e : E) :
    Decidable (G.Incident v e) := inferInstanceAs (Decidable (G.left e = v ∨ G.right e = v))

def IsPerfectMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v, ∃! e, e ∈ M ∧ G.Incident v e

abbrev Matching (G : LooplessGraph V E) := {M : Finset E // G.IsPerfectMatching M}

instance matchingFintype (G : LooplessGraph V E) : Fintype G.Matching :=
  Fintype.ofFinite _

def indicator (G : LooplessGraph V E) (M : G.Matching) (e : E) : ℝ :=
  if e ∈ M.val then 1 else 0

def polytope (G : LooplessGraph V E) : Set (E → ℝ) :=
  convexHull ℝ (Set.range G.indicator)

end LooplessGraph
end MatchingEntropyBounds
end

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.LooplessGraph

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def Crosses (G : LooplessGraph V E) (S : Finset V) (e : E) : Prop :=
  (G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)

instance crossesDecidable (G : LooplessGraph V E) (S : Finset V) (e : E) :
    Decidable (G.Crosses S e) := inferInstanceAs (Decidable
      ((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.left e ∉ S ∧ G.right e ∈ S)))

def cut (G : LooplessGraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (G.Crosses S)

def degree (G : LooplessGraph V E) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, if G.Incident v e then x e else 0

def cutMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e ∈ G.cut S, x e

end MatchingEntropyBounds.LooplessGraph
end

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

section TriangleExpansion
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def triangleTip (v : V) (i : Fin 3) : V ⊕ Fin 2 := ![Sum.inl v, Sum.inr 0, Sum.inr 1] i

def triangleCollapse (v : V) : V ⊕ Fin 2 → V := Sum.elim id (fun _ => v)

def reattach (v : V) (i : Fin 3) (w : V) : V ⊕ Fin 2 :=
  if w = v then triangleTip v i else Sum.inl w

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem collapse_reattach (v : V) (i : Fin 3) (w : V) :
    triangleCollapse v (reattach v i w) = w := by
  by_cases h : w = v
  · subst w
    fin_cases i <;> simp [reattach,triangleTip,triangleCollapse]
  · simp [reattach,h,triangleCollapse]

def triangleExpansion (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    LooplessGraph (V ⊕ Fin 2) (E ⊕ Fin 3) where
  left := Sum.elim (fun e => reattach v (c e) (G.left e)) (fun i => triangleTip v (i + 1))
  right := Sum.elim (fun e => reattach v (c e) (G.right e)) (fun i => triangleTip v (i + 2))
  loopless := by
    intro e h
    rcases e with e | i
    · have hh := congrArg (triangleCollapse v) h
      exact G.loopless e ((collapse_reattach v (c e) (G.left e)).symm.trans
        (hh.trans (collapse_reattach v (c e) (G.right e))))
    · fin_cases i <;> simp [triangleTip] at h

def triangleVertices (v : V) : Finset (V ⊕ Fin 2) := Finset.univ.image (triangleTip v)

end TriangleExpansion
end MatchingEntropyBounds.Refined
end

namespace CanonicalFace198

variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

def facesThrough (P : Set A) (x : A) : Set (Set A) :=
  {F | Convex ℝ F ∧ IsExtreme ℝ P F ∧ x ∈ F}

def minFace (P : Set A) (x : A) : Set A := ⋂₀ facesThrough P x

end CanonicalFace198

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def LocalLabels (G : LooplessGraph V E) (v : V) (c : E → Fin 3) : Prop :=
  ∀ i, ∃! e, G.Incident v e ∧ c e = i

def localEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) : E := Classical.choose (hc i)

def localExtension (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) : (E → ℝ) →ₗ[ℝ] (E ⊕ Fin 3 → ℝ) where
  toFun x := Sum.elim x (fun i => x (localEdge G c v hc i))
  map_add' x y := by ext e; cases e <;> rfl
  map_smul' a x := by ext e; cases e <;> rfl

def oldRestriction : (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun y e := y (Sum.inl e)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TriangleFace198

end

noncomputable section
open scoped BigOperators
open MatchingEntropyBounds MatchingEntropyBounds.Refined
namespace TriangleFace198
universe uV uE
variable {V : Type uV} {E : Type uE} [instFintypeV : Fintype V] [Fintype E] [DecidableEq V] [instDecidableEqE : DecidableEq E]

theorem existsLocalLabels (G : LooplessGraph V E) (v : V)
    (hcard : Fintype.card {e : E // G.Incident v e} = 3) :
    ∃ c : E → Fin 3, LocalLabels G v c := by
  classical
  let e : {e : E // G.Incident v e} ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let c : E → Fin 3 := fun e' => if h : G.Incident v e' then e ⟨e', h⟩ else 0
  refine ⟨c, ?_⟩
  intro i
  refine ⟨(e.symm i : {e : E // G.Incident v e}).1, ?_, ?_⟩
  · constructor
    · exact (e.symm i).2
    · simp [c, (e.symm i).2]
  · rintro e' ⟨hinc, hc⟩
    have hval : e ⟨e', hinc⟩ = i := by
      simpa [c, hinc] using hc
    calc
      e' = (e.symm (e ⟨e', hinc⟩) : {e : E // G.Incident v e}).1 := by simp
      _ = (e.symm i : {e : E // G.Incident v e}).1 := by rw [hval]
lemma triangleTip_mem_triangleVertices (v : V) (i : Fin 3) :
    triangleTip v i ∈ triangleVertices v :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
lemma sum_inl_mem_triangleVertices (v w : V) :
    (Sum.inl w : V ⊕ Fin 2) ∈ triangleVertices v ↔ w = v := by
  classical
  constructor
  · intro h
    rw [triangleVertices, Finset.mem_image] at h
    obtain ⟨i, -, hi⟩ := h
    fin_cases i
    · simp [triangleTip] at hi
      exact hi.symm
    · simp [triangleTip] at hi
    · simp [triangleTip] at hi
  · rintro rfl
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [triangleTip]⟩
lemma reattach_mem_triangleVertices {v : V} {i : Fin 3} {w : V} :
    reattach v i w ∈ triangleVertices v ↔ w = v := by
  classical
  by_cases h : w = v
  · subst w
    simp [reattach, triangleTip_mem_triangleVertices]
  · simp [reattach, h, sum_inl_mem_triangleVertices]
lemma crosses_inl_iff (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (e : E) :
    MatchingEntropyBounds.LooplessGraph.Crosses (triangleExpansion G c v) (triangleVertices v) (Sum.inl e) ↔ G.Incident v e := by
  classical
  unfold MatchingEntropyBounds.LooplessGraph.Crosses
  simp only [triangleExpansion, Sum.elim_inl]
  rw [reattach_mem_triangleVertices, reattach_mem_triangleVertices]
  constructor
  · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩)
    · exact Or.inl hl
    · exact Or.inr hr
  · rintro (hl | hr)
    · exact Or.inl ⟨hl, fun hrv => G.loopless e (hl.trans hrv.symm)⟩
    · exact Or.inr ⟨fun hlv => G.loopless e (hlv.trans hr.symm), hr⟩
lemma not_crosses_inr (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (i : Fin 3) :
    ¬MatchingEntropyBounds.LooplessGraph.Crosses (triangleExpansion G c v) (triangleVertices v) (Sum.inr i) := by
  classical
  intro h
  unfold MatchingEntropyBounds.LooplessGraph.Crosses at h
  simp only [triangleExpansion, Sum.elim_inr] at h
  exact h.elim (fun h' => h'.2 (triangleTip_mem_triangleVertices v (i + 2)))
    (fun h' => h'.1 (triangleTip_mem_triangleVertices v (i + 1)))
theorem cutMass_triangleVertices (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (y : E ⊕ Fin 3 → ℝ) :
    MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) =
      ∑ e : E, if G.Incident v e then y (Sum.inl e) else 0 := by
  classical
  rw [MatchingEntropyBounds.LooplessGraph.cutMass, MatchingEntropyBounds.LooplessGraph.cut, Finset.sum_filter, Fintype.sum_sum_type]
  have hnew : (∑ i : Fin 3,
      (if MatchingEntropyBounds.LooplessGraph.Crosses (triangleExpansion G c v) (triangleVertices v) (Sum.inr i)
        then y (Sum.inr i) else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [not_crosses_inr G c v i]
  rw [hnew, add_zero]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : G.Incident v e <;> simp [crosses_inl_iff, h]
lemma triangleTip_injective (v : V) : Function.Injective (triangleTip (V := V) v) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangleTip]
lemma tip_eq_tip {v : V} {i j : Fin 3} : triangleTip v i = triangleTip v j ↔ i = j :=
  ⟨fun h => triangleTip_injective v h, fun h => by rw [h]⟩
lemma sum_inl_eq_tip_iff {v w : V} {i : Fin 3} :
    (Sum.inl w : V ⊕ Fin 2) = triangleTip v i ↔ w = v ∧ i = 0 := by
  fin_cases i <;> simp [triangleTip]
lemma tip_eq_sum_inl_iff {v w : V} {i : Fin 3} :
    triangleTip (V := V) v i = (Sum.inl w : V ⊕ Fin 2) ↔ v = w ∧ i = 0 := by
  rw [eq_comm, sum_inl_eq_tip_iff, eq_comm (a := v)]
lemma fin3_add_eq_iff_ne (k j : Fin 3) : (j + 1 = k ∨ j + 2 = k) ↔ k ≠ j := by
  revert k j; decide
lemma fin3_exists_ne_two (i j : Fin 3) (h : i ≠ j) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  revert i j; decide
lemma fin3_ne_add_one (i : Fin 3) : i + 1 ≠ i := by revert i; decide
lemma fin3_ne_add_two (i : Fin 3) : i + 2 ≠ i := by revert i; decide
lemma fin3_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide
lemma fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
lemma fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide
lemma fin3_eq_one_or_two (j : Fin 3) (h : j ≠ 0) : j = 1 ∨ j = 2 := by
  have hv : j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
  rcases hv with h1 | h2
  · exact Or.inl (Fin.ext (by simpa using h1))
  · exact Or.inr (Fin.ext (by simpa using h2))
lemma incident_tip_inr (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (k j : Fin 3) :
    (triangleExpansion G c v).Incident (triangleTip v k) (Sum.inr j) ↔ k ≠ j := by
  unfold MatchingEntropyBounds.LooplessGraph.Incident
  simp only [triangleExpansion, Sum.elim_inr, tip_eq_tip]
  exact fin3_add_eq_iff_ne k j
lemma incident_tip_inl (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (k : Fin 3) (e : E) :
    (triangleExpansion G c v).Incident (triangleTip v k) (Sum.inl e) ↔
      G.Incident v e ∧ c e = k := by
  unfold MatchingEntropyBounds.LooplessGraph.Incident
  simp only [triangleExpansion, Sum.elim_inl, reattach]
  constructor
  · rintro (h | h)
    · by_cases hl : G.left e = v
      · rw [if_pos hl] at h
        exact ⟨Or.inl hl, triangleTip_injective v h⟩
      · rw [if_neg hl] at h
        obtain ⟨hw, -⟩ := (sum_inl_eq_tip_iff).mp h
        exact absurd hw hl
    · by_cases hr : G.right e = v
      · rw [if_pos hr] at h
        exact ⟨Or.inr hr, triangleTip_injective v h⟩
      · rw [if_neg hr] at h
        obtain ⟨hw, -⟩ := (sum_inl_eq_tip_iff).mp h
        exact absurd hw hr
  · rintro ⟨hinc, hc⟩
    rcases hinc with hl | hr
    · left; rw [if_pos hl, hc]
    · right; rw [if_pos hr, hc]
lemma incident_inl_inr (G : LooplessGraph V E) (c : E → Fin 3) (v w : V) (j : Fin 3) :
    (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inr j) ↔ w = v ∧ j ≠ 0 := by
  unfold MatchingEntropyBounds.LooplessGraph.Incident
  simp only [triangleExpansion, Sum.elim_inr]
  constructor
  · rintro (h | h)
    · obtain ⟨hw, hi⟩ := (tip_eq_sum_inl_iff).mp h
      refine ⟨hw.symm, ?_⟩
      rw [← hi]
      exact (fin3_ne_add_one j).symm
    · obtain ⟨hw, hi⟩ := (tip_eq_sum_inl_iff).mp h
      refine ⟨hw.symm, ?_⟩
      rw [← hi]
      exact (fin3_ne_add_two j).symm
  · rintro ⟨rfl, hj⟩
    rcases fin3_eq_one_or_two j hj with rfl | rfl
    · right; simp [triangleTip]
    · left; simp [triangleTip]
lemma reattach_of_ne {v w : V} (hw : w ≠ v) (i : Fin 3) :
    reattach v i w = Sum.inl w := by
  simp [reattach, hw]
lemma reattach_of_eq (v : V) (i : Fin 3) :
    reattach v i v = triangleTip v i := by
  simp [reattach]
lemma incident_inl_inl_of_ne (G : LooplessGraph V E) (c : E → Fin 3) (v w : V) (e : E)
    (hw : w ≠ v) :
    (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inl e) ↔ G.Incident w e := by
  unfold MatchingEntropyBounds.LooplessGraph.Incident
  simp only [triangleExpansion, Sum.elim_inl]
  constructor
  · rintro (h | h)
    · by_cases hl : G.left e = v
      · rw [hl, reattach_of_eq] at h
        obtain ⟨hvw, -⟩ := (tip_eq_sum_inl_iff).mp h
        exact absurd hvw.symm hw
      · rw [reattach_of_ne hl] at h
        exact Or.inl (Sum.inl.inj h)
    · by_cases hr : G.right e = v
      · rw [hr, reattach_of_eq] at h
        obtain ⟨hvw, -⟩ := (tip_eq_sum_inl_iff).mp h
        exact absurd hvw.symm hw
      · rw [reattach_of_ne hr] at h
        exact Or.inr (Sum.inl.inj h)
  · rintro (hl | hr)
    · left
      rw [reattach_of_ne (w := G.left e) (fun h => hw (hl.symm.trans h)), hl]
    · right
      rw [reattach_of_ne (w := G.right e) (fun h => hw (hr.symm.trans h)), hr]
lemma fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by revert i; decide
def fin2to3 (i : Fin 2) : Fin 3 := ⟨i.val + 1, by omega⟩
lemma fin2to3_injective : Function.Injective fin2to3 := by
  intro i j h
  have : i.val + 1 = j.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)
lemma fin2to3_val (i : Fin 2) : (fin2to3 i).val = i.val + 1 := rfl
lemma fin2to3_ne_zero (i : Fin 2) : fin2to3 i ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [fin2to3_val] at this
lemma triangle_edge_unique (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M)
    {j j' : Fin 3} (hj : Sum.inr j ∈ M) (hj' : Sum.inr j' ∈ M) : j = j' := by
  by_contra hne
  obtain ⟨k, hkj, hkj'⟩ := fin3_exists_ne_two j j' hne
  have hspec1 : Sum.inr j ∈ M ∧ (triangleExpansion G c v).Incident (triangleTip v k) (Sum.inr j) :=
    ⟨hj, (incident_tip_inr G c v k j).mpr hkj⟩
  have hspec2 : Sum.inr j' ∈ M ∧ (triangleExpansion G c v).Incident (triangleTip v k) (Sum.inr j') :=
    ⟨hj', (incident_tip_inr G c v k j').mpr hkj'⟩
  exact hne (Sum.inr.inj ((hM (triangleTip v k)).unique hspec1 hspec2))
lemma triangleTip_zero (v : V) : triangleTip v 0 = (Sum.inl v : V ⊕ Fin 2) := by
  simp [triangleTip]
lemma triangleTip_one (v : V) : triangleTip v 1 = (Sum.inr 0 : V ⊕ Fin 2) := by
  simp [triangleTip]
lemma triangleTip_two (v : V) : triangleTip v 2 = (Sum.inr 1 : V ⊕ Fin 2) := by
  simp [triangleTip]
lemma tip_of_inr_eq (v : V) (k : Fin 3) (i : Fin 2) :
    triangleTip v k = (Sum.inr i : V ⊕ Fin 2) ↔ k = fin2to3 i := by
  constructor
  · intro h
    have hk : triangleTip v k = triangleTip v (fin2to3 i) := by
      rw [h]
      fin_cases i <;> rfl
    exact triangleTip_injective v hk
  · rintro rfl
    fin_cases i <;> rfl
lemma inr_eq_tip_iff (v : V) (k : Fin 3) (i : Fin 2) :
    (Sum.inr i : V ⊕ Fin 2) = triangleTip v k ↔ k = fin2to3 i := by
  rw [eq_comm, tip_of_inr_eq]
lemma exists_tip_of_inr (v : V) (z : V ⊕ Fin 2) (h : ∃ i : Fin 2, z = Sum.inr i) :
    ∃ k : Fin 3, z = triangleTip v k := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨fin2to3 i, (inr_eq_tip_iff v (fin2to3 i) i).mpr rfl⟩
lemma sum_inl_eq_tip_zero_iff (v w : V) :
    (Sum.inl w : V ⊕ Fin 2) = triangleTip v 0 ↔ w = v := by
  rw [triangleTip_zero, Sum.inl.injEq]
lemma exists_incident_old_of_matching (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M) :
    ∃ e : E, Sum.inl e ∈ M ∧ G.Incident v e := by
  by_contra h
  push_neg at h
  have key : ∀ k : Fin 3, ∃ j : Fin 3, Sum.inr j ∈ M ∧ k ≠ j := by
    intro k
    obtain ⟨e, ⟨heM, hinc⟩, -⟩ := hM (triangleTip v k)
    rcases e with e | j
    · exact absurd ((incident_tip_inl G c v k e).mp hinc).1 (h e heM)
    · exact ⟨j, heM, (incident_tip_inr G c v k j).mp hinc⟩
  obtain ⟨j0, hj0M, h0⟩ := key 0
  obtain ⟨j1, hj1M, h1⟩ := key 1
  obtain ⟨j2, hj2M, h2⟩ := key 2
  have e01 : j0 = j1 := triangle_edge_unique G c v hM hj0M hj1M
  have e02 : j0 = j2 := triangle_edge_unique G c v hM hj0M hj2M
  rw [← e01] at h1
  rw [← e02] at h2
  rcases fin3_cases j0 with rfl | rfl | rfl
  · exact h0 rfl
  · exact h1 rfl
  · exact h2 rfl
lemma one_le_of_mem_convexHull {F : Type*} [AddCommGroup F] [Module ℝ F]
    (L : F →ₗ[ℝ] ℝ) {S : Set F} (hS : ∀ s ∈ S, 1 ≤ L s) {y : F}
    (hy : y ∈ convexHull ℝ S) : 1 ≤ L y := by
  obtain ⟨ι, hι, w, z, hw0, hw1, hzS, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hy
  letI := hι
  have hLy : L y = ∑ i, w i * L (z i) := by
    rw [← hsum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [smul_eq_mul]
  rw [hLy]
  calc (1:ℝ) = ∑ i, w i := hw1.symm
    _ = ∑ i, w i * 1 := by simp
    _ ≤ ∑ i, w i * L (z i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hS (z i) (hzS i)) (hw0 i)
lemma convexHull_section_eq {F : Type*} [AddCommGroup F] [Module ℝ F]
    (L : F →ₗ[ℝ] ℝ) (S : Set F) (hS : ∀ s ∈ S, 1 ≤ L s) :
    convexHull ℝ S ∩ {y | L y = 1} = convexHull ℝ {s | s ∈ S ∧ L s = 1} := by
  refine subset_antisymm ?_ ?_
  · rintro y ⟨hyHull, hyL⟩
    obtain ⟨ι, hι, w, z, hw0, hw1, hzS, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hyHull
    letI := hι
    let t : Finset ι := Finset.univ.filter (fun i => L (z i) = 1)
    have h_nonneg : ∀ i, 0 ≤ w i * (L (z i) - 1) :=
      fun i => mul_nonneg (hw0 i) (sub_nonneg.mpr (hS _ (hzS i)))
    have h_sum_zero : ∑ i, w i * (L (z i) - 1) = 0 := by
      have hsplit : ∑ i, w i * (L (z i) - 1) = ∑ i, w i * L (z i) - ∑ i, w i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsplit, hw1]
      have hLsum : ∑ i, w i * L (z i) = 1 := by
        have hLy' : L y = ∑ i, w i * L (z i) := by
          rw [← hsum, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          simp [smul_eq_mul]
        rw [← hLy', hyL]
      rw [hLsum]
      ring
    have h_each : ∀ i, w i * (L (z i) - 1) = 0 :=
      fun i => (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) (fun j _ => h_nonneg j)).mp h_sum_zero i (Finset.mem_univ i)
    have hwzero : ∀ i, i ∉ t → w i = 0 := by
      intro i hi
      have hne : L (z i) ≠ 1 := by
        intro h
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      rcases mul_eq_zero.mp (h_each i) with hw | hL
      · exact hw
      · exact absurd (sub_eq_zero.mp hL) hne
    have hsum_t : ∑ i ∈ t, w i = 1 := by
      rw [← hw1]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => hwzero i hi)
    have hsum_t_z : ∑ i ∈ t, w i • z i = y := by
      rw [← hsum]
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun i _ hi => by rw [hwzero i hi, zero_smul])
    refine mem_convexHull_of_exists_fintype (fun i : {i // i ∈ t} => w i.1)
      (fun i : {i // i ∈ t} => z i.1) ?_ ?_ ?_ ?_
    · intro i; exact hw0 i.1
    · rw [Finset.sum_coe_sort t w]; exact hsum_t
    · intro i
      have hi : L (z i.1) = 1 := (Finset.mem_filter.mp i.2).2
      exact ⟨hzS i.1, hi⟩
    · rw [Finset.sum_coe_sort t (fun i => w i • z i)]
      exact hsum_t_z
  · apply convexHull_min
    · intro s hs
      exact ⟨subset_convexHull ℝ S hs.1, hs.2⟩
    · exact (convex_convexHull ℝ S).inter (convex_hyperplane L.isLinear 1)
def cutLinear (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    (E ⊕ Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun y := MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v)
  map_add' y z := by
    simp [MatchingEntropyBounds.LooplessGraph.cutMass, Finset.sum_add_distrib]
  map_smul' a y := by
    simp [MatchingEntropyBounds.LooplessGraph.cutMass, Finset.mul_sum]
lemma cutLinear_apply (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (y : E ⊕ Fin 3 → ℝ) :
    cutLinear G c v y = MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) := rfl
lemma cutLinear_eq_sum (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (y : E ⊕ Fin 3 → ℝ) :
    cutLinear G c v y = ∑ e : E, if G.Incident v e then y (Sum.inl e) else 0 := by
  rw [cutLinear_apply, cutMass_triangleVertices]
lemma localEdge_spec (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) :
    G.Incident v (localEdge G c v hc i) ∧ c (localEdge G c v hc i) = i :=
  (Classical.choose_spec (hc i)).1
lemma localEdge_unique (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (i : Fin 3) {e : E}
    (hinc : G.Incident v e) (hlab : c e = i) : e = localEdge G c v hc i :=
  (Classical.choose_spec (hc i)).2 e ⟨hinc, hlab⟩
lemma indicator_inl_nonneg {G : LooplessGraph V E} {c : E → Fin 3} {v : V}
    (M : (triangleExpansion G c v).Matching) (e : E) :
    0 ≤ (if G.Incident v e then (triangleExpansion G c v).indicator M (Sum.inl e) else 0) := by
  by_cases h : G.Incident v e
  · rw [if_pos h]
    unfold MatchingEntropyBounds.LooplessGraph.indicator
    split_ifs <;> norm_num
  · rw [if_neg h]
lemma one_le_cutMass_indicator {G : LooplessGraph V E} {c : E → Fin 3} {v : V}
    (M : (triangleExpansion G c v).Matching) :
    1 ≤ MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v)
      ((triangleExpansion G c v).indicator M) (triangleVertices v) := by
  obtain ⟨e0, he0M, hinc0⟩ := exists_incident_old_of_matching G c v M.2
  rw [cutMass_triangleVertices]
  have hsingle : (if G.Incident v e0 then (triangleExpansion G c v).indicator M (Sum.inl e0) else 0) = 1 := by
    rw [if_pos hinc0]
    unfold MatchingEntropyBounds.LooplessGraph.indicator
    rw [if_pos he0M]
  calc (1:ℝ) = (if G.Incident v e0 then (triangleExpansion G c v).indicator M (Sum.inl e0) else 0) := hsingle.symm
    _ ≤ ∑ e, if G.Incident v e then (triangleExpansion G c v).indicator M (Sum.inl e) else 0 :=
        Finset.single_le_sum (fun e _ => indicator_inl_nonneg M e) (Finset.mem_univ e0)
lemma one_le_cutMass_of_mem_polytope {G : LooplessGraph V E} {c : E → Fin 3} {v : V}
    {y : E ⊕ Fin 3 → ℝ} (hy : y ∈ (triangleExpansion G c v).polytope) :
    1 ≤ MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) := by
  have h := one_le_of_mem_convexHull (cutLinear G c v)
    (S := Set.range (triangleExpansion G c v).indicator) ?_ hy
  · rwa [cutLinear_apply] at h
  · rintro s ⟨M, rfl⟩
    rw [cutLinear_apply]
    exact one_le_cutMass_indicator M
lemma convex_polytope_cut_eq_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    Convex ℝ {y | y ∈ (triangleExpansion G c v).polytope ∧
      MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) = 1} := by
  have h1 : Convex ℝ (triangleExpansion G c v).polytope := convex_convexHull ℝ _
  have h2 : Convex ℝ {y : E ⊕ Fin 3 → ℝ |
      MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) = 1} := by
    have := convex_hyperplane (cutLinear G c v).isLinear 1
    simpa [cutLinear_apply] using this
  exact h1.inter h2
lemma isExtreme_polytope_cut_eq_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V) :
    IsExtreme ℝ (triangleExpansion G c v).polytope
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) = 1} := by
  refine ⟨fun y hy => hy.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hlx : 1 ≤ MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) x (triangleVertices v) :=
    one_le_cutMass_of_mem_polytope hx
  have hly : 1 ≤ MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) :=
    one_le_cutMass_of_mem_polytope hy
  have hlin : MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) (a • x + b • y) (triangleVertices v) =
      a * MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) x (triangleVertices v) +
      b * MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) := by
    simp [MatchingEntropyBounds.LooplessGraph.cutMass, Finset.mul_sum, Finset.sum_add_distrib]
  have hz2 : a * MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) x (triangleVertices v) +
      b * MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) = 1 := by
    rw [← hlin]; exact hz.2
  have hxL' : MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) x (triangleVertices v) = 1 := by
    nlinarith [hlx, hly, hz2, ha, hb]
  exact ⟨hx, hxL'⟩
lemma incident_inl_inl_of_eq (G : LooplessGraph V E) (c : E → Fin 3) (v : V) (e : E) :
    (triangleExpansion G c v).Incident (Sum.inl v) (Sum.inl e) ↔ G.Incident v e ∧ c e = 0 := by
  unfold MatchingEntropyBounds.LooplessGraph.Incident
  simp only [triangleExpansion, Sum.elim_inl]
  constructor
  · rintro (h | h)
    · by_cases hl : G.left e = v
      · rw [hl, reattach_of_eq] at h
        exact ⟨Or.inl hl, ((tip_eq_sum_inl_iff).mp h).2⟩
      · rw [reattach_of_ne hl] at h
        exact absurd (Sum.inl.inj h) hl
    · by_cases hr : G.right e = v
      · rw [hr, reattach_of_eq] at h
        exact ⟨Or.inr hr, ((tip_eq_sum_inl_iff).mp h).2⟩
      · rw [reattach_of_ne hr] at h
        exact absurd (Sum.inl.inj h) hr
  · rintro ⟨hinc, hc0⟩
    rcases hinc with hl | hr
    · left; rw [hl, reattach_of_eq, hc0, triangleTip_zero]
    · right; rw [hr, reattach_of_eq, hc0, triangleTip_zero]
def matchingEdgeAt (G : LooplessGraph V E) {M : Finset E} (hM : G.IsPerfectMatching M) (w : V) : E :=
  Classical.choose (hM w)
lemma matchingEdgeAt_mem (G : LooplessGraph V E) {M : Finset E} (hM : G.IsPerfectMatching M) (w : V) :
    matchingEdgeAt G hM w ∈ M :=
  (Classical.choose_spec (hM w)).1.1
lemma matchingEdgeAt_incident (G : LooplessGraph V E) {M : Finset E} (hM : G.IsPerfectMatching M) (w : V) :
    G.Incident w (matchingEdgeAt G hM w) :=
  (Classical.choose_spec (hM w)).1.2
lemma eq_matchingEdgeAt (G : LooplessGraph V E) {M : Finset E} (hM : G.IsPerfectMatching M) (w : V)
    {e : E} (he : e ∈ M) (hinc : G.Incident w e) : e = matchingEdgeAt G hM w :=
  (Classical.choose_spec (hM w)).2 e ⟨he, hinc⟩
lemma indicator_of_mem (G : LooplessGraph V E) (M : G.Matching) {e : E} (h : e ∈ M.val) :
    G.indicator M e = 1 := by
  simp [MatchingEntropyBounds.LooplessGraph.indicator, h]
lemma indicator_of_not_mem (G : LooplessGraph V E) (M : G.Matching) {e : E} (h : e ∉ M.val) :
    G.indicator M e = 0 := by
  simp [MatchingEntropyBounds.LooplessGraph.indicator, h]
def expandSet (M : Finset E) (i : Fin 3) : Finset (E ⊕ Fin 3) :=
  M.image Sum.inl ∪ {Sum.inr i}
lemma mem_expandSet {M : Finset E} {i : Fin 3} {x : E ⊕ Fin 3} :
    x ∈ expandSet M i ↔ (∃ e ∈ M, x = Sum.inl e) ∨ x = Sum.inr i := by
  simp only [expandSet, Finset.mem_union, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro (⟨e, he, rfl⟩ | h)
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr h
  · rintro (⟨e, he, hx⟩ | h)
    · exact Or.inl ⟨e, he, hx.symm⟩
    · exact Or.inr h
lemma mem_expandSet_inl {M : Finset E} {i : Fin 3} {e : E} :
    Sum.inl e ∈ expandSet M i ↔ e ∈ M := by
  rw [mem_expandSet]
  constructor
  · rintro (⟨e', he', h⟩ | h)
    · exact Sum.inl.inj h ▸ he'
    · exact absurd h Sum.inl_ne_inr
  · intro he
    exact Or.inl ⟨e, he, rfl⟩
lemma mem_expandSet_inr {M : Finset E} {i j : Fin 3} :
    Sum.inr j ∈ expandSet M i ↔ j = i := by
  rw [mem_expandSet]
  constructor
  · rintro (⟨e, -, h⟩ | h)
    · exact absurd h.symm Sum.inl_ne_inr
    · exact Sum.inr.inj h
  · rintro rfl
    exact Or.inr rfl
lemma expandSet_covers_tip (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {N : Finset E} (hN : G.IsPerfectMatching N) (k : Fin 3) :
    ∃! x : E ⊕ Fin 3, x ∈ expandSet N (c (matchingEdgeAt G hN v)) ∧
      (triangleExpansion G c v).Incident (triangleTip v k) x := by
  classical
  set e0 := matchingEdgeAt G hN v with he0def
  have he0N : e0 ∈ N := matchingEdgeAt_mem G hN v
  have he0inc : G.Incident v e0 := matchingEdgeAt_incident G hN v
  by_cases hk : k = c e0
  · refine ⟨Sum.inl e0, ⟨(mem_expandSet_inl).mpr he0N, ?_⟩, ?_⟩
    · exact (incident_tip_inl G c v k e0).mpr ⟨he0inc, hk.symm⟩
    · rintro x ⟨hxM, hxinc⟩
      rcases x with e | j
      · obtain ⟨hinc, hlab⟩ := (incident_tip_inl G c v k e).mp hxinc
        have hmem : e ∈ N := (mem_expandSet_inl).mp hxM
        have : e = e0 := eq_matchingEdgeAt G hN v hmem hinc
        rw [this]
      · have hj : j = c e0 := (mem_expandSet_inr).mp hxM
        have hne : k ≠ j := (incident_tip_inr G c v k j).mp hxinc
        exact absurd hk (by rw [hj] at hne; exact hne)
  · refine ⟨Sum.inr (c e0), ⟨(mem_expandSet_inr).mpr rfl, ?_⟩, ?_⟩
    · exact (incident_tip_inr G c v k (c e0)).mpr (fun h => hk h)
    · rintro x ⟨hxM, hxinc⟩
      rcases x with e | j
      · obtain ⟨hinc, hlab⟩ := (incident_tip_inl G c v k e).mp hxinc
        have hmem : e ∈ N := (mem_expandSet_inl).mp hxM
        have h1 : e = e0 := eq_matchingEdgeAt G hN v hmem hinc
        rw [h1] at hlab
        exact absurd hlab.symm hk
      · have hj : j = c e0 := (mem_expandSet_inr).mp hxM
        rw [hj]
lemma not_incident_inr_inl (G : LooplessGraph V E) (c : E → Fin 3) (v w : V) (i : Fin 3)
    (hw : w ≠ v) :
    ¬(triangleExpansion G c v).Incident (Sum.inl w) (Sum.inr i) := by
  rw [incident_inl_inr]
  exact fun h => hw h.1
lemma expandSet_covers_old (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {N : Finset E} (hN : G.IsPerfectMatching N) (i0 : Fin 3) (w : V) (hw : w ≠ v) :
    ∃! x : E ⊕ Fin 3, x ∈ expandSet N i0 ∧
      (triangleExpansion G c v).Incident (Sum.inl w) x := by
  refine ⟨Sum.inl (matchingEdgeAt G hN w), ⟨(mem_expandSet_inl).mpr (matchingEdgeAt_mem G hN w), ?_⟩, ?_⟩
  · rw [incident_inl_inl_of_ne G c v w _ hw]
    exact matchingEdgeAt_incident G hN w
  · rintro x ⟨hxM, hxinc⟩
    rcases x with e | j
    · rw [incident_inl_inl_of_ne G c v w e hw] at hxinc
      have hmem : e ∈ N := (mem_expandSet_inl).mp hxM
      have : e = matchingEdgeAt G hN w := (Classical.choose_spec (hN w)).2 e ⟨hmem, hxinc⟩
      rw [this]
    · exact absurd hxinc (not_incident_inr_inl G c v w j hw)
lemma tips_cover_expandSet (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {N : Finset E} (hN : G.IsPerfectMatching N) (i : Fin 2) :
    ∃! x : E ⊕ Fin 3, x ∈ expandSet N (c (matchingEdgeAt G hN v)) ∧
      (triangleExpansion G c v).Incident (Sum.inr i) x := by
  have h := expandSet_covers_tip G c v hN (fin2to3 i)
  have htip : triangleTip v (fin2to3 i) = (Sum.inr i : V ⊕ Fin 2) := by
    rw [eq_comm, inr_eq_tip_iff]
  simpa [htip] using h
lemma tips_cover_expandSet_i0 (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {N : Finset E} (hN : G.IsPerfectMatching N) (i0 : Fin 3)
    (hi0 : i0 = c (matchingEdgeAt G hN v)) (i : Fin 2) :
    ∃! x : E ⊕ Fin 3, x ∈ expandSet N i0 ∧
      (triangleExpansion G c v).Incident (Sum.inr i) x := by
  rw [hi0]
  exact tips_cover_expandSet G c v hN i
lemma expandSet_perfect (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {N : Finset E} (hN : G.IsPerfectMatching N) (i0 : Fin 3)
    (hi0 : i0 = c (matchingEdgeAt G hN v)) :
    (triangleExpansion G c v).IsPerfectMatching (expandSet N i0) := by
  classical
  intro p
  rcases p with w | i
  · by_cases hw : w = v
    · rw [hw]
      have h := expandSet_covers_tip G c v hN 0
      rw [← hi0] at h
      have htip : triangleTip v (0 : Fin 3) = (Sum.inl v : V ⊕ Fin 2) := triangleTip_zero v
      simpa [htip] using h
    · exact expandSet_covers_old G c v hN i0 w hw
  · exact tips_cover_expandSet_i0 G c v hN i0 hi0 i
def coverEdge (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M)
    (p : V ⊕ Fin 2) : E ⊕ Fin 3 := Classical.choose (hM p)
lemma coverEdge_mem (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M) (p : V ⊕ Fin 2) :
    coverEdge G c v hM p ∈ M := (Classical.choose_spec (hM p)).1.1
lemma coverEdge_incident (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M) (p : V ⊕ Fin 2) :
    (triangleExpansion G c v).Incident p (coverEdge G c v hM p) :=
  (Classical.choose_spec (hM p)).1.2
lemma coverEdge_unique (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    {M : Finset (E ⊕ Fin 3)} (hM : (triangleExpansion G c v).IsPerfectMatching M) (p : V ⊕ Fin 2)
    {x : E ⊕ Fin 3} (hx : x ∈ M) (hinc : (triangleExpansion G c v).Incident p x) :
    x = coverEdge G c v hM p :=
  (Classical.choose_spec (hM p)).2 x ⟨hx, hinc⟩
lemma incident_old_unique_of_mass_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (M : (triangleExpansion G c v).Matching)
    (hL : cutLinear G c v ((triangleExpansion G c v).indicator M) = 1)
    {e e' : E} (he : Sum.inl e ∈ M.val) (hinc : G.Incident v e)
    (he' : Sum.inl e' ∈ M.val) (hinc' : G.Incident v e') : e = e' := by
  by_contra hne
  set f : E → ℝ := fun x => if G.Incident v x then (triangleExpansion G c v).indicator M (Sum.inl x) else 0 with hf
  have hf0 : ∀ x, 0 ≤ f x := fun x => indicator_inl_nonneg M x
  have hfe : f e = 1 := by
    simp only [hf, if_pos hinc]
    exact indicator_of_mem (triangleExpansion G c v) M he
  have hfe' : f e' = 1 := by
    simp only [hf, if_pos hinc']
    exact indicator_of_mem (triangleExpansion G c v) M he'
  have hpair : ∑ x ∈ ({e, e'} : Finset E), f x = 2 := by
    rw [Finset.sum_pair hne, hfe, hfe']
    norm_num
  have hle : ∑ x ∈ ({e, e'} : Finset E), f x ≤ ∑ x : E, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (by simp) (fun x _ _ => hf0 x)
  have hL' : ∑ x : E, f x = 1 := by
    have := hL
    rw [cutLinear_eq_sum] at this
    simpa [hf] using this
  linarith
lemma triangle_edge_eq_of_mass_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (M : (triangleExpansion G c v).Matching)
    {e0 : E} (he0 : Sum.inl e0 ∈ M.val) (hinc0 : G.Incident v e0)
    {j : Fin 3} (hj : Sum.inr j ∈ M.val) : j = c e0 := by
  by_contra hne
  have htipne : c e0 ≠ j := fun h => hne h.symm
  have h1 : Sum.inl e0 = coverEdge G c v M.2 (triangleTip v (c e0)) :=
    coverEdge_unique G c v M.2 _ he0 ((incident_tip_inl G c v (c e0) e0).mpr ⟨hinc0, rfl⟩)
  have h2 : Sum.inr j = coverEdge G c v M.2 (triangleTip v (c e0)) :=
    coverEdge_unique G c v M.2 _ hj ((incident_tip_inr G c v (c e0) j).mpr htipne)
  exact Sum.inl_ne_inr (h1.trans h2.symm)
lemma triangle_edge_exists_of_mass_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (M : (triangleExpansion G c v).Matching)
    (hL : cutLinear G c v ((triangleExpansion G c v).indicator M) = 1)
    {e0 : E} (he0 : Sum.inl e0 ∈ M.val) (hinc0 : G.Incident v e0) :
    ∃ j : Fin 3, Sum.inr j ∈ M.val := by
  by_contra h
  push_neg at h
  have h0 : ∃ e : E, Sum.inl e ∈ M.val ∧ G.Incident v e ∧ c e = 0 := by
    have hc := coverEdge_incident G c v M.2 (triangleTip v (0 : Fin 3))
    have hmem := coverEdge_mem G c v M.2 (triangleTip v (0 : Fin 3))
    rcases x : coverEdge G c v M.2 (triangleTip v (0 : Fin 3)) with e | j
    · have := (incident_tip_inl G c v 0 e).mp (x ▸ hc)
      exact ⟨e, x ▸ hmem, this⟩
    · exact absurd (x ▸ hmem) (h j)
  have h1 : ∃ e : E, Sum.inl e ∈ M.val ∧ G.Incident v e ∧ c e = 1 := by
    have hc := coverEdge_incident G c v M.2 (triangleTip v (1 : Fin 3))
    have hmem := coverEdge_mem G c v M.2 (triangleTip v (1 : Fin 3))
    rcases x : coverEdge G c v M.2 (triangleTip v (1 : Fin 3)) with e | j
    · have := (incident_tip_inl G c v 1 e).mp (x ▸ hc)
      exact ⟨e, x ▸ hmem, this⟩
    · exact absurd (x ▸ hmem) (h j)
  obtain ⟨e, he, hince, hce⟩ := h0
  obtain ⟨e', he', hince', hce'⟩ := h1
  have hlab : c e ≠ c e' := by rw [hce, hce']; norm_num
  exact hlab (congrArg c (incident_old_unique_of_mass_one G c v M hL he hince he' hince'))
lemma mem_openSegment_linear_image_iff {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] {f : A →ₗ[ℝ] B} (hf : Function.Injective f)
    (a b s : A) :
    f s ∈ openSegment ℝ (f a) (f b) ↔ s ∈ openSegment ℝ a b := by
  constructor
  · rintro ⟨α, β, hα, hβ, hsum, heq⟩
    refine ⟨α, β, hα, hβ, hsum, ?_⟩
    apply hf
    rw [map_add, map_smul, map_smul]
    exact heq
  · rintro ⟨α, β, hα, hβ, hsum, rfl⟩
    exact ⟨α, β, hα, hβ, hsum, by rw [map_add, map_smul, map_smul]⟩
theorem minFace_linear_image {A B : Type*} [AddCommGroup A] [Module ℝ A]
    [AddCommGroup B] [Module ℝ B] (P : Set A) (R : Set B) (f : A →ₗ[ℝ] B)
    (g : B →ₗ[ℝ] A) (hP : Convex ℝ P) (hR : Convex ℝ R)
    (hQext : IsExtreme ℝ R (f '' P)) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, y ∈ f '' P → f (g y) = y) :
    ∀ x, x ∈ P → CanonicalFace198.minFace R (f x) = f '' CanonicalFace198.minFace P x := by
  intro x hx
  classical
  set Q : Set B := f '' P with hQdef
  have hQext' : IsExtreme ℝ R Q := hQext
  have hfinj : Function.Injective f := by
    intro a b hab
    calc a = g (f a) := (hgf a).symm
      _ = g (f b) := by rw [hab]
      _ = b := hgf b
  have hQsubR : Q ⊆ R := hQext'.subset
  have hfxQ : f x ∈ Q := ⟨x, hx, rfl⟩
  have hfxR : f x ∈ R := hQsubR hfxQ
  -- faces of R inside Q are faces of Q
  have key₁ : ∀ F : Set B, F ⊆ Q → (IsExtreme ℝ R F ↔ IsExtreme ℝ Q F) := by
    intro F hFQ
    constructor
    · intro hRF
      refine ⟨hFQ, ?_⟩
      intro y₁ hy₁ y₂ hy₂ z hzF hz
      exact hRF.left_mem_of_mem_openSegment (hQsubR hy₁) (hQsubR hy₂) hzF hz
    · intro hQF
      refine ⟨hFQ.trans hQsubR, ?_⟩
      intro y₁ hy₁ y₂ hy₂ z hzF hz
      have hy₁Q : y₁ ∈ Q := hQext'.left_mem_of_mem_openSegment hy₁ hy₂ (hFQ hzF) hz
      have hy₂Q : y₂ ∈ Q := hQext'.right_mem_of_mem_openSegment hy₁ hy₂ (hFQ hzF) hz
      exact hQF.left_mem_of_mem_openSegment hy₁Q hy₂Q hzF hz
  -- image transfer: faces of P map to faces of Q
  have key₂ : ∀ S : Set A, S ⊆ P → (IsExtreme ℝ P S ↔ IsExtreme ℝ Q (f '' S)) := by
    intro S hSP
    constructor
    · intro hPS
      refine ⟨Set.image_mono hSP, ?_⟩
      intro y₁ hy₁ y₂ hy₂ z hz hzseg
      obtain ⟨a, haP, rfl⟩ := hy₁
      obtain ⟨b, hbP, rfl⟩ := hy₂
      obtain ⟨s, hsS, rfl⟩ := hz
      have hseg : s ∈ openSegment ℝ a b :=
        (mem_openSegment_linear_image_iff hfinj a b s).1 hzseg
      exact ⟨a, hPS.left_mem_of_mem_openSegment haP hbP hsS hseg, rfl⟩
    · intro hQS
      refine ⟨hSP, ?_⟩
      intro a haP b hbP s hsS hseg
      have hfseg : f s ∈ openSegment ℝ (f a) (f b) :=
        (mem_openSegment_linear_image_iff hfinj a b s).2 hseg
      have hfa : f a ∈ f '' P := ⟨a, haP, rfl⟩
      have hfb : f b ∈ f '' P := ⟨b, hbP, rfl⟩
      have hfs : f s ∈ f '' S := ⟨s, hsS, rfl⟩
      obtain ⟨s', hs'S, hs'⟩ := hQS.left_mem_of_mem_openSegment hfa hfb hfs hfseg
      have hsa : s' = a := hfinj hs'
      rwa [hsa] at hs'S
  -- minFace of P at x
  have hPself : P ∈ CanonicalFace198.facesThrough P x := ⟨hP, IsExtreme.refl ℝ P, hx⟩
  have hNsubP : CanonicalFace198.minFace P x ⊆ P :=
    Set.sInter_subset_of_mem hPself
  have hNext : IsExtreme ℝ P (CanonicalFace198.minFace P x) :=
    isExtreme_sInter ⟨P, hPself⟩ (fun F hF => hF.2.1)
  have hNconv : Convex ℝ (CanonicalFace198.minFace P x) :=
    convex_sInter (fun F hF => hF.1)
  have hxN : x ∈ CanonicalFace198.minFace P x :=
    Set.mem_sInter.2 (fun F hF => hF.2.2)
  -- M := minFace of R at f x
  set M : Set B := CanonicalFace198.minFace R (f x) with hMdef
  have hRself : R ∈ CanonicalFace198.facesThrough R (f x) := ⟨hR, IsExtreme.refl ℝ R, hfxR⟩
  have hMext : IsExtreme ℝ R M :=
    isExtreme_sInter ⟨R, hRself⟩ (fun F hF => hF.2.1)
  have hMconv : Convex ℝ M := convex_sInter (fun F hF => hF.1)
  have hfxM : f x ∈ M := Set.mem_sInter.2 (fun F hF => hF.2.2)
  have hQface : Q ∈ CanonicalFace198.facesThrough R (f x) :=
    ⟨hP.linear_image f, hQext', hfxQ⟩
  have hMsubQ : M ⊆ Q := Set.sInter_subset_of_mem hQface
  -- M is the minFace of Q at f x
  have hMextQ : IsExtreme ℝ Q M := (key₁ M hMsubQ).1 hMext
  have hM_eq_minQ : M = CanonicalFace198.minFace Q (f x) := by
    refine subset_antisymm ?_ ?_
    · refine Set.subset_sInter ?_
      intro F hF
      exact Set.sInter_subset_of_mem
        ⟨hF.1, (key₁ F hF.2.1.subset).2 hF.2.1, hF.2.2⟩
    · have hMQ : M ∈ CanonicalFace198.facesThrough Q (f x) := ⟨hMconv, hMextQ, hfxM⟩
      exact Set.sInter_subset_of_mem hMQ
  have hstepA : ∀ S ∈ CanonicalFace198.facesThrough P x,
      f '' S ∈ CanonicalFace198.facesThrough Q (f x) := by
    rintro S ⟨hSconv, hSext, hxS⟩
    exact ⟨hSconv.linear_image f, (key₂ S hSext.subset).1 hSext, ⟨x, hxS, rfl⟩⟩
  have keyQ : ∀ F : Set B, F ⊆ Q → f '' (g '' F) = F := by
    intro F hFQ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y', hy', rfl⟩ := hz
      rw [hfg y' (hFQ hy')]
      exact hy'
    · intro hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hfg y (hFQ hy)⟩
  have hstepB : ∀ F ∈ CanonicalFace198.facesThrough Q (f x),
      ∃ S ∈ CanonicalFace198.facesThrough P x, F = f '' S := by
    rintro F ⟨hFconv, hFext, hxF⟩
    have hFQ : F ⊆ Q := hFext.subset
    have hgFP : g '' F ⊆ P := by
      rintro a ⟨y, hy, rfl⟩
      obtain ⟨p, hp, hfp⟩ := hFQ hy
      rw [← hfp, hgf p]
      exact hp
    have hSextP : IsExtreme ℝ P (g '' F) := by
      refine (key₂ (g '' F) hgFP).2 ?_
      rw [keyQ F hFQ]
      exact hFext
    exact ⟨g '' F, ⟨hFconv.linear_image g, hSextP, ⟨f x, hxF, hgf x⟩⟩, (keyQ F hFQ).symm⟩
  have himg_int : f '' (⋂₀ CanonicalFace198.facesThrough P x) =
      ⋂₀ CanonicalFace198.facesThrough Q (f x) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact Set.mem_sInter.2 (fun F hF => by
        obtain ⟨S, hS, rfl⟩ := hstepB F hF
        exact ⟨p, Set.mem_sInter.1 hp S hS, rfl⟩)
    · intro hy
      have hyQ : y ∈ Q := Set.mem_sInter.1 hy Q (hstepA P hPself)
      obtain ⟨p, hpP, rfl⟩ := hyQ
      refine ⟨p, Set.mem_sInter.2 (fun S hS => ?_), rfl⟩
      obtain ⟨p', hp', hfp'⟩ := Set.mem_sInter.1 hy (f '' S) (hstepA S hS)
      exact (hfinj hfp') ▸ hp'
  rw [hM_eq_minQ]
  exact himg_int.symm
lemma minFace_transport_consumer (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c)
    (hPQ : localExtension G c v hc '' G.polytope =
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1})
    (hQext : IsExtreme ℝ (triangleExpansion G c v).polytope
      {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1})
    (hgf : ∀ x, oldRestriction (localExtension G c v hc x) = x)
    (hfg : ∀ y ∈ {y | y ∈ (triangleExpansion G c v).polytope ∧
        (triangleExpansion G c v).cutMass y (triangleVertices v) = 1},
      localExtension G c v hc (oldRestriction y) = y) :
    ∀ x ∈ G.polytope,
      CanonicalFace198.minFace (triangleExpansion G c v).polytope
          (localExtension G c v hc x) =
        localExtension G c v hc '' CanonicalFace198.minFace G.polytope x := by
  intro x hx
  -- Pin the fully qualified expansion symbol: source projections prune declarations by
  -- resolvable reference, and `triangleExpansion` lives in an opened namespace.
  have hpin : (_root_.OAI.MatchingEntropyBounds.Refined.triangleExpansion G c v).polytope
      = (triangleExpansion G c v).polytope := rfl
  refine minFace_linear_image G.polytope (triangleExpansion G c v).polytope
    (localExtension G c v hc) oldRestriction (convex_convexHull ℝ _)
    (convex_convexHull ℝ _) ?_ hgf ?_ x hx
  · rwa [hPQ]
  · intro y hy
    exact hfg y (hPQ ▸ hy)
def oldPart (M : Finset (E ⊕ Fin 3)) : Finset E :=
  Finset.univ.filter (fun e => Sum.inl e ∈ M)
lemma mem_oldPart {M : Finset (E ⊕ Fin 3)} {e : E} :
    e ∈ oldPart M ↔ Sum.inl e ∈ M := by
  classical
  simp [oldPart]
lemma oldPart_perfect (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (M : (triangleExpansion G c v).Matching)
    (hL : cutLinear G c v ((triangleExpansion G c v).indicator M) = 1) :
    G.IsPerfectMatching (oldPart M.val) := by
  classical
  obtain ⟨e0, he0M, hinc0⟩ := exists_incident_old_of_matching G c v M.2
  have huniq : ∀ {e e' : E}, Sum.inl e ∈ M.val → G.Incident v e →
      Sum.inl e' ∈ M.val → G.Incident v e' → e = e' :=
    fun he hinc he' hinc' => incident_old_unique_of_mass_one G c v M hL he hinc he' hinc'
  intro w
  by_cases hw : w = v
  · subst w
    refine ⟨e0, ⟨(mem_oldPart).mpr he0M, hinc0⟩, ?_⟩
    rintro e ⟨heN, hinc⟩
    exact huniq ((mem_oldPart).mp heN) hinc he0M hinc0
  · have hxmem := coverEdge_mem G c v M.2 (Sum.inl w)
    have hxinc := coverEdge_incident G c v M.2 (Sum.inl w)
    rcases hx : coverEdge G c v M.2 (Sum.inl w) with e | j
    · have hinc : G.Incident w e :=
        (incident_inl_inl_of_ne G c v w e hw).mp (hx ▸ hxinc)
      refine ⟨e, ⟨(mem_oldPart).mpr (hx ▸ hxmem), hinc⟩, ?_⟩
      rintro e' ⟨he'N, hinc'⟩
      have he'M : Sum.inl e' ∈ M.val := (mem_oldPart).mp he'N
      have hincH : (triangleExpansion G c v).Incident (Sum.inl w) (Sum.inl e') :=
        (incident_inl_inl_of_ne G c v w e' hw).mpr hinc'
      have hcov : Sum.inl e' = coverEdge G c v M.2 (Sum.inl w) :=
        coverEdge_unique G c v M.2 _ he'M hincH
      rw [hx] at hcov
      exact Sum.inl.inj hcov
    · exact absurd (hx ▸ hxinc) (not_incident_inr_inl G c v w j hw)
lemma indicator_eq_localExtension_of_mass_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (M : (triangleExpansion G c v).Matching)
    (hL : cutLinear G c v ((triangleExpansion G c v).indicator M) = 1) :
    (triangleExpansion G c v).indicator M =
      localExtension G c v hc
        (G.indicator ⟨oldPart M.val, oldPart_perfect G c v M hL⟩) := by
  classical
  obtain ⟨e0, he0M, hinc0⟩ := exists_incident_old_of_matching G c v M.2
  have huniq : ∀ {e e' : E}, Sum.inl e ∈ M.val → G.Incident v e →
      Sum.inl e' ∈ M.val → G.Incident v e' → e = e' :=
    fun he hinc he' hinc' => incident_old_unique_of_mass_one G c v M hL he hinc he' hinc'
  obtain ⟨j0, hj0M⟩ := triangle_edge_exists_of_mass_one G c v M hL he0M hinc0
  have hj0 : j0 = c e0 := triangle_edge_eq_of_mass_one G c v M he0M hinc0 hj0M
  have hj0M' : Sum.inr (c e0) ∈ M.val := hj0 ▸ hj0M
  have htri : ∀ j : Fin 3, Sum.inr j ∈ M.val ↔ j = c e0 := by
    intro j
    constructor
    · intro hj
      exact triangle_edge_eq_of_mass_one G c v M he0M hinc0 hj
    · rintro rfl
      exact hj0M'
  have hle0 : localEdge G c v hc (c e0) = e0 :=
    (localEdge_unique G c v hc (c e0) hinc0 rfl).symm
  funext x
  rcases x with e | j
  · simp [MatchingEntropyBounds.LooplessGraph.indicator, localExtension, mem_oldPart]
  · have hiff : Sum.inr j ∈ M.val ↔ localEdge G c v hc j ∈ oldPart M.val := by
      constructor
      · intro hj
        have hjc : j = c e0 := (htri j).mp hj
        have hle : localEdge G c v hc j = e0 := by
          rw [hjc]
          exact hle0
        rw [hle]
        exact (mem_oldPart).mpr he0M
      · intro hmem
        have hle_inc : G.Incident v (localEdge G c v hc j) := (localEdge_spec G c v hc j).1
        have heq : localEdge G c v hc j = e0 :=
          huniq ((mem_oldPart).mp hmem) hle_inc he0M hinc0
        have hj : j = c e0 := by
          rw [← heq]
          exact ((localEdge_spec G c v hc j).2).symm
        exact (htri j).mpr hj
    by_cases h : Sum.inr j ∈ M.val
    · have h2 : localEdge G c v hc j ∈ oldPart M.val := hiff.mp h
      simp [MatchingEntropyBounds.LooplessGraph.indicator, localExtension, h, h2]
    · have h2 : localEdge G c v hc j ∉ oldPart M.val := fun hc' => h (hiff.mpr hc')
      simp [MatchingEntropyBounds.LooplessGraph.indicator, localExtension, h, h2]
lemma cutLinear_indicator_expandSet (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (N : G.Matching) :
    cutLinear G c v ((triangleExpansion G c v).indicator
      ⟨expandSet N.val (c (matchingEdgeAt G N.2 v)),
        expandSet_perfect G c v N.2 (c (matchingEdgeAt G N.2 v)) rfl⟩) = 1 := by
  classical
  rw [cutLinear_eq_sum]
  have he0N : matchingEdgeAt G N.2 v ∈ N.val := matchingEdgeAt_mem G N.2 v
  have hinc0 : G.Incident v (matchingEdgeAt G N.2 v) := matchingEdgeAt_incident G N.2 v
  have huniq : ∀ e : E, G.Incident v e → e ∈ N.val → e = matchingEdgeAt G N.2 v := by
    intro e hinc heN
    exact (Classical.choose_spec (N.2 v)).2 e ⟨heN, hinc⟩
  refine (Finset.sum_eq_single (matchingEdgeAt G N.2 v) ?_ ?_).trans ?_
  · intro e _ hne
    by_cases hinc : G.Incident v e
    · rw [if_pos hinc]
      have hnot : e ∉ N.val := fun heN => hne (huniq e hinc heN)
      simp [MatchingEntropyBounds.LooplessGraph.indicator, mem_expandSet_inl, hnot]
    · rw [if_neg hinc]
  · intro h
    exact absurd (Finset.mem_univ (matchingEdgeAt G N.2 v)) h
  · rw [if_pos hinc0]
    simp [MatchingEntropyBounds.LooplessGraph.indicator, mem_expandSet_inl, he0N]
lemma localExtension_indicator_eq (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) (N : G.Matching) (i0 : Fin 3)
    (hi0 : i0 = c (matchingEdgeAt G N.2 v)) :
    localExtension G c v hc (G.indicator N) =
      (triangleExpansion G c v).indicator
        ⟨expandSet N.val i0,
          expandSet_perfect G c v N.2 i0 hi0⟩ := by
  classical
  set e0 := matchingEdgeAt G N.2 v with he0def
  have he0N : e0 ∈ N.val := matchingEdgeAt_mem G N.2 v
  have hinc0 : G.Incident v e0 := matchingEdgeAt_incident G N.2 v
  have huniq : ∀ e : E, G.Incident v e → e ∈ N.val → e = e0 := by
    intro e hinc heN
    exact (Classical.choose_spec (N.2 v)).2 e ⟨heN, hinc⟩
  have hle0 : localEdge G c v hc i0 = e0 := by
    rw [hi0]
    exact (localEdge_unique G c v hc (c e0) hinc0 rfl).symm
  funext x
  rcases x with e | i
  · simp only [localExtension, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl,
      MatchingEntropyBounds.LooplessGraph.indicator, mem_expandSet_inl]
  · have hiff : i = i0 ↔ localEdge G c v hc i ∈ N.val := by
      constructor
      · rintro rfl
        rw [hle0]
        exact he0N
      · intro hmem
        have hinc : G.Incident v (localEdge G c v hc i) := (localEdge_spec G c v hc i).1
        have heq : localEdge G c v hc i = e0 := huniq _ hinc hmem
        calc i = c (localEdge G c v hc i) := ((localEdge_spec G c v hc i).2).symm
          _ = c e0 := by rw [heq]
          _ = i0 := hi0.symm
    by_cases h : i = i0
    · have hmem : localEdge G c v hc i ∈ N.val := hiff.mp h
      simp only [localExtension, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
        MatchingEntropyBounds.LooplessGraph.indicator]
      rw [if_pos hmem, if_pos ((mem_expandSet_inr).mpr h)]
    · have hmem : localEdge G c v hc i ∉ N.val := fun hm => h (hiff.mpr hm)
      have hnot : Sum.inr i ∉ expandSet N.val i0 := fun hm => h ((mem_expandSet_inr).mp hm)
      simp only [localExtension, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inr,
        MatchingEntropyBounds.LooplessGraph.indicator]
      rw [if_neg hmem, if_neg hnot]
lemma image_polytope_subset_cut_one (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) :
    localExtension G c v hc '' G.polytope ⊆
      {y | y ∈ (triangleExpansion G c v).polytope ∧ cutLinear G c v y = 1} := by
  classical
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨ι, hι, w, z, hw0, hw1, hzS, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
  letI := hι
  choose N hN using hzS
  have hz : ∀ i, z i = G.indicator (N i) := fun i => (hN i).symm
  have hfx : localExtension G c v hc x =
      ∑ i, w i • (triangleExpansion G c v).indicator
        ⟨expandSet (N i).val (c (matchingEdgeAt G (N i).2 v)),
          expandSet_perfect G c v (N i).2 (c (matchingEdgeAt G (N i).2 v)) rfl⟩ := by
    rw [← hsum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hz i, localExtension_indicator_eq G c v hc (N i) _ rfl]
  constructor
  · have hmem : localExtension G c v hc x ∈ convexHull ℝ (Set.range (triangleExpansion G c v).indicator) := by
      refine mem_convexHull_of_exists_fintype w
        (fun i => (triangleExpansion G c v).indicator
          ⟨expandSet (N i).val (c (matchingEdgeAt G (N i).2 v)),
            expandSet_perfect G c v (N i).2 (c (matchingEdgeAt G (N i).2 v)) rfl⟩)
        hw0 hw1 ?_ hfx.symm
      intro i
      exact ⟨_, rfl⟩
    exact hmem
  · rw [hfx, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc ∑ i, w i * cutLinear G c v ((triangleExpansion G c v).indicator
          ⟨expandSet (N i).val (c (matchingEdgeAt G (N i).2 v)),
            expandSet_perfect G c v (N i).2 (c (matchingEdgeAt G (N i).2 v)) rfl⟩)
        = ∑ i, w i * 1 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [cutLinear_indicator_expandSet]
        _ = 1 := by simpa using hw1
lemma one_le_cutLinear_indicator (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (M : (triangleExpansion G c v).Matching) :
    1 ≤ cutLinear G c v ((triangleExpansion G c v).indicator M) := by
  rw [cutLinear_apply]
  exact one_le_cutMass_indicator M
lemma mass_one_generators_eq (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) :
    {s | s ∈ Set.range (triangleExpansion G c v).indicator ∧ cutLinear G c v s = 1} =
      localExtension G c v hc '' Set.range G.indicator := by
  classical
  ext s
  constructor
  · rintro ⟨⟨M, rfl⟩, hL⟩
    have hN := oldPart_perfect G c v M hL
    exact ⟨G.indicator ⟨oldPart M.val, hN⟩, ⟨_, rfl⟩,
      (indicator_eq_localExtension_of_mass_one G c v hc M hL).symm⟩
  · rintro ⟨x, ⟨N, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · exact ⟨⟨expandSet N.val (c (matchingEdgeAt G N.2 v)),
        expandSet_perfect G c v N.2 (c (matchingEdgeAt G N.2 v)) rfl⟩,
        (localExtension_indicator_eq G c v hc N _ rfl).symm⟩
    · rw [localExtension_indicator_eq G c v hc N _ rfl]
      exact cutLinear_indicator_expandSet G c v N
lemma cut_one_image_eq (G : LooplessGraph V E) (c : E → Fin 3) (v : V)
    (hc : LocalLabels G v c) :
    {y | y ∈ (triangleExpansion G c v).polytope ∧ cutLinear G c v y = 1} =
      localExtension G c v hc '' G.polytope := by
  classical
  have hS : ∀ s ∈ Set.range (triangleExpansion G c v).indicator, 1 ≤ cutLinear G c v s := by
    rintro s ⟨M, rfl⟩
    exact one_le_cutLinear_indicator G c v M
  have hsec := convexHull_section_eq (cutLinear G c v) (Set.range (triangleExpansion G c v).indicator) hS
  have hgen := mass_one_generators_eq G c v hc
  have himg : localExtension G c v hc '' G.polytope =
      convexHull ℝ (localExtension G c v hc '' Set.range G.indicator) := by
    rw [MatchingEntropyBounds.LooplessGraph.polytope, LinearMap.image_convexHull]
  show convexHull ℝ (Set.range (triangleExpansion G c v).indicator) ∩ {y | cutLinear G c v y = 1} = _
  rw [hsec, hgen, himg]
theorem triangle_expansion_face {V : Type uV} {E : Type uE}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : LooplessGraph V E) (v : V)
    (hdeg : Fintype.card {e : E // G.Incident v e} = 3)
    (_hmatching : Nonempty G.Matching) :
    ∃ (c : E → Fin 3) (hc : LocalLabels G v c),
      let H := triangleExpansion G c v
      let f := localExtension G c v hc
      let Q := {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1}
      f '' G.polytope = Q ∧
      Convex ℝ Q ∧ IsExtreme ℝ H.polytope Q ∧
      (∀ x, oldRestriction (f x) = x) ∧
      (∀ y ∈ Q, f (oldRestriction y) = y) ∧
      (∀ x e, f x (Sum.inl e) = x e) ∧
      (∀ x i, f x (Sum.inr i) = x (localEdge G c v hc i)) ∧
      (∀ x, (∀ e, x e = (1/3 : ℝ)) → ∀ e, f x e = (1/3 : ℝ)) ∧
      (∀ x ∈ G.polytope, CanonicalFace198.minFace H.polytope (f x) = f '' CanonicalFace198.minFace G.polytope x)  := by
  classical
  obtain ⟨c, hc⟩ := existsLocalLabels G v hdeg
  refine ⟨c, hc, ?_⟩
  dsimp only
  have hfg : ∀ y ∈ {y | y ∈ (triangleExpansion G c v).polytope ∧
      MatchingEntropyBounds.LooplessGraph.cutMass (triangleExpansion G c v) y (triangleVertices v) = 1},
      localExtension G c v hc (oldRestriction y) = y := by
    intro y hy
    have hy' : y ∈ localExtension G c v hc '' G.polytope := by
      rw [← cut_one_image_eq G c v hc]
      exact ⟨hy.1, by rw [cutLinear_apply]; exact hy.2⟩
    obtain ⟨x, -, rfl⟩ := hy'
    rfl
  have hgf : ∀ x, oldRestriction (localExtension G c v hc x) = x := by
    intro x
    rfl
  refine ⟨?_, convex_polytope_cut_eq_one G c v, isExtreme_polytope_cut_eq_one G c v,
    hgf, hfg, ?_, ?_, ?_, ?_⟩
  · rw [← cut_one_image_eq G c v hc]
    rfl
  · intro x e
    rfl
  · intro x i
    rfl
  · intro x hx e
    cases e <;> simp [localExtension, hx]
  · exact minFace_transport_consumer G c v hc (by rw [← cut_one_image_eq G c v hc]; rfl)
      (isExtreme_polytope_cut_eq_one G c v) hgf hfg
end TriangleFace198
end

end OAI
