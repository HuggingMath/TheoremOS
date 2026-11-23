import ArchivedTriangleFace

open scoped BigOperators
open OAI.MatchingEntropyBounds OAI.MatchingEntropyBounds.Refined OAI.TriangleFace198

namespace TheoremOS.WeightedTriangleMatching

variable {Vertex Edge : Type*}
  [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex] [DecidableEq Edge]

def cost (weights point : Edge → ℝ) : ℝ :=
  ∑ edge, weights edge * point edge

/-- A triangle expansion preserves every attainable cost under a budget on the original
edges, when the expanded matching polytope is restricted to cut mass one. -/
theorem attainable_costs_eq (G : LooplessGraph Vertex Edge) (v : Vertex)
    (degreeThree : Fintype.card {e : Edge // G.Incident v e} = 3)
    (hasMatching : Nonempty G.Matching) :
    ∃ labels : Edge → Fin 3, ∀ (price usage : Edge → ℝ) (budget : ℝ),
      let H := triangleExpansion G labels v
      cost price '' {x | x ∈ G.polytope ∧ cost usage x ≤ budget} =
        (fun y => cost price (oldRestriction y)) ''
          {y | y ∈ H.polytope ∧ H.cutMass y (triangleVertices v) = 1 ∧
            cost usage (oldRestriction y) ≤ budget} := by
  obtain ⟨labels, localLabels, faceMap, _, _, restrictExtension, _⟩ :=
    triangle_expansion_face G v degreeThree hasMatching
  refine ⟨labels, ?_⟩
  intro price usage budget
  dsimp only
  ext value
  constructor
  · rintro ⟨x, ⟨hx, withinBudget⟩, rfl⟩
    have inFace := Set.mem_image_of_mem (localExtension G labels v localLabels) hx
    rw [faceMap] at inFace
    exact ⟨localExtension G labels v localLabels x,
      ⟨inFace.1, inFace.2, by simpa only [restrictExtension] using withinBudget⟩,
      congrArg (cost price) (restrictExtension x)⟩
  · rintro ⟨y, ⟨hy, cutOne, withinBudget⟩, rfl⟩
    have inImage : y ∈ localExtension G labels v localLabels '' G.polytope := by
      rw [faceMap]
      exact ⟨hy, cutOne⟩
    obtain ⟨x, hx, rfl⟩ := inImage
    exact ⟨x, ⟨hx, by simpa only [restrictExtension] using withinBudget⟩,
      (congrArg (cost price) (restrictExtension x)).symm⟩

#print axioms attainable_costs_eq

end TheoremOS.WeightedTriangleMatching
