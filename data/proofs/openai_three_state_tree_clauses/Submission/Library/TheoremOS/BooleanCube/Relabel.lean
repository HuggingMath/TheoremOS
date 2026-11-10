import Submission.Library.TheoremOS.BooleanCube.Sensitivity

/-!
# Relabelling coordinates

An equivalence `e : ι ≃ κ` of coordinate types induces `cubeMap e : (ι → Bool) ≃ (κ → Bool)`,
`(cubeMap e x) k = x (e.symm k)`, and `relabel e f = f ∘ cubeMap e`. Every measure in this library
is invariant: `(relabel e f)^ S = f̂ (e S)`, degree, ±1-valuedness, influences, total influence,
level-one coefficients, sensitivity, block sensitivity and certificate complexity. Use it to move a
construction on `Fin a × Fin b`, `Fin a ⊕ Fin b`, … to `Fin n` (via `Fintype.equivFin` or
`finProdFinEquiv`, `finSumFinEquiv`).

Sources: R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014, §1–2
(the measures are defined coordinate-free). Textbook material.

Bridges: `relabel e f x = f (fun k => x (e.symm k))` (`relabel_apply`); `relabel e.symm (relabel e f) = f`
(`relabel_symm_relabel`).
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

noncomputable section

variable {ι κ : Type*}

/-- Transport a point of the cube along `e`. -/
def cubeMap (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) := e.arrowCongr (Equiv.refl Bool)

@[simp] lemma cubeMap_apply (e : ι ≃ κ) (x : ι → Bool) (k : κ) : cubeMap e x k = x (e.symm k) := rfl

@[simp] lemma cubeMap_symm_apply (e : ι ≃ κ) (y : κ → Bool) (i : ι) : (cubeMap e).symm y i = y (e i) := rfl

/-- `relabel e f`: the function `f` on `κ`-cubes read on `ι`-cubes. -/
def relabel {β : Type*} (e : ι ≃ κ) (f : (κ → Bool) → β) (x : ι → Bool) : β := f (cubeMap e x)

lemma relabel_apply {β : Type*} (e : ι ≃ κ) (f : (κ → Bool) → β) (x : ι → Bool) :
    relabel e f x = f (fun k => x (e.symm k)) := rfl

@[simp] lemma relabel_symm_relabel {β : Type*} (e : ι ≃ κ) (f : (κ → Bool) → β) :
    relabel e.symm (relabel e f) = f := by
  funext y; unfold relabel; congr 1; funext k; simp

lemma IsBooleanValued.relabel {f : (κ → Bool) → ℝ} (hf : IsBooleanValued f) (e : ι ≃ κ) :
    IsBooleanValued (BooleanCube.relabel e f) := fun _ => hf _

lemma character_map_cubeMap (e : ι ≃ κ) (S : Finset ι) (x : ι → Bool) :
    character (S.map e.toEmbedding) (cubeMap e x) = character S x := by
  simp [character, prod_map]

@[simp] lemma cubeMap_symm_cubeMap (e : ι ≃ κ) (x : ι → Bool) : cubeMap e.symm (cubeMap e x) = x := by
  funext i; simp

lemma average_comp_equiv_of_equiv {α γ : Type*} [Fintype α] [Fintype γ] (e : α ≃ γ) (g : γ → ℝ) :
    average (fun a => g (e a)) = average g := by
  unfold average; rw [Fintype.card_congr e, e.sum_comp]

lemma sup_comp_equiv {α γ : Type*} [Fintype α] [Fintype γ] (e : α ≃ γ) (g : γ → ℕ) :
    (univ.sup fun a => g (e a)) = univ.sup g := by
  apply le_antisymm
  · exact Finset.sup_le fun a _ => le_sup (f := g) (mem_univ (e a))
  · refine Finset.sup_le fun c _ => ?_
    have := le_sup (f := fun a => g (e a)) (mem_univ (e.symm c))
    simpa using this

section Decidable

variable [DecidableEq ι] [DecidableEq κ]

lemma cubeMap_flip (e : ι ≃ κ) (i : ι) (x : ι → Bool) : cubeMap e (flip i x) = flip (e i) (cubeMap e x) := by
  funext k
  by_cases h : k = e i
  · subst h; simp
  · rw [flip_apply_of_ne h, cubeMap_apply, cubeMap_apply, flip_apply_of_ne]
    rwa [Ne, Equiv.symm_apply_eq]

lemma cubeMap_flipSet (e : ι ≃ κ) (B : Finset ι) (x : ι → Bool) :
    cubeMap e (flipSet B x) = flipSet (B.map e.toEmbedding) (cubeMap e x) := by
  funext k
  simp only [cubeMap_apply, flipSet_apply, mem_map_equiv]

variable [Fintype ι] [Fintype κ]

/-- `(relabel e f)^ S = f̂ (e S)`. -/
theorem fourierCoeff_relabel (e : ι ≃ κ) (f : (κ → Bool) → ℝ) (S : Finset ι) :
    fourierCoeff (relabel e f) S = fourierCoeff f (S.map e.toEmbedding) := by
  unfold fourierCoeff
  rw [← average_comp_equiv_of_equiv (cubeMap e)]
  simp only [relabel, character_map_cubeMap]

lemma fourierCoeff_relabel_singleton (e : ι ≃ κ) (f : (κ → Bool) → ℝ) (i : ι) :
    fourierCoeff (relabel e f) {i} = fourierCoeff f {e i} := by
  rw [fourierCoeff_relabel, map_singleton]; rfl

lemma sum_fourierCoeff_relabel_singleton (e : ι ≃ κ) (f : (κ → Bool) → ℝ) (g : ℝ → ℝ) :
    ∑ i, g (fourierCoeff (relabel e f) {i}) = ∑ k, g (fourierCoeff f {k}) := by
  simp only [fourierCoeff_relabel_singleton]
  exact e.sum_comp fun k => g (fourierCoeff f {k})

theorem degree_relabel (e : ι ≃ κ) (f : (κ → Bool) → ℝ) : degree (relabel e f) = degree f := by
  apply le_antisymm
  · rw [degree_le_iff]; intro S hS
    rw [fourierCoeff_relabel] at hS
    simpa using card_le_degree hS
  · rw [degree_le_iff]; intro T hT
    have hmap : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by ext k; simp
    have hT' : fourierCoeff (relabel e f) (T.map e.symm.toEmbedding) ≠ 0 := by
      rw [fourierCoeff_relabel, hmap]; exact hT
    simpa using card_le_degree hT'

theorem influence_relabel (e : ι ≃ κ) (f : (κ → Bool) → ℝ) (i : ι) :
    influence i (relabel e f) = influence (e i) f := by
  unfold influence
  rw [← average_comp_equiv_of_equiv (cubeMap e)]
  simp only [relabel, cubeMap_flip]

theorem totalInfluence_relabel (e : ι ≃ κ) (f : (κ → Bool) → ℝ) :
    totalInfluence (relabel e f) = totalInfluence f := by
  unfold totalInfluence
  simp only [influence_relabel]
  exact e.sum_comp fun k => influence k f

end Decidable

namespace Query

variable {β : Type*}

lemma IsCertificate.relabel {f : (κ → Bool) → β} {x : ι → Bool} {C : Finset κ} (e : ι ≃ κ)
    (hC : IsCertificate f (cubeMap e x) C) : IsCertificate (BooleanCube.relabel e f) x (C.map e.symm.toEmbedding) := by
  intro z hz
  show f (cubeMap e z) = f (cubeMap e x)
  apply hC
  intro k hk
  simpa using hz (e.symm k) (mem_map_of_mem _ hk)

theorem certificateComplexityAt_relabel_le [Fintype κ] (f : (κ → Bool) → β) (e : ι ≃ κ) (x : ι → Bool) :
    certificateComplexityAt (BooleanCube.relabel e f) x ≤ certificateComplexityAt f (cubeMap e x) := by
  obtain ⟨C, hC, hcard⟩ := exists_isCertificate_card_eq f (cubeMap e x)
  rw [← hcard, ← card_map e.symm.toEmbedding]
  exact certificateComplexityAt_le_card (hC.relabel e)

theorem certificateComplexityAt_relabel [Fintype ι] [Fintype κ] (f : (κ → Bool) → β) (e : ι ≃ κ) (x : ι → Bool) :
    certificateComplexityAt (BooleanCube.relabel e f) x = certificateComplexityAt f (cubeMap e x) := by
  refine le_antisymm (certificateComplexityAt_relabel_le f e x) ?_
  have := certificateComplexityAt_relabel_le (BooleanCube.relabel e f) e.symm (cubeMap e x)
  rwa [relabel_symm_relabel, cubeMap_symm_cubeMap] at this

variable [DecidableEq ι] [DecidableEq κ]

lemma isSensitiveFamily_relabel [DecidableEq β] {f : (κ → Bool) → β} {x : ι → Bool} {F : Finset (Finset ι)}
    (e : ι ≃ κ) (hF : IsSensitiveFamily (BooleanCube.relabel e f) x F) :
    IsSensitiveFamily f (cubeMap e x) (F.image fun B => B.map e.toEmbedding) := by
  refine ⟨?_, ?_⟩
  · simp only [mem_image]
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ hAB
    rw [disjoint_map]
    exact hF.1 A hA B hB fun h => hAB (h ▸ rfl)
  · simp only [mem_image]
    rintro _ ⟨B, hB, rfl⟩
    rw [← cubeMap_flipSet]
    exact hF.2 B hB

variable [Fintype ι] [Fintype κ]

theorem certificateComplexity_relabel (f : (κ → Bool) → β) (e : ι ≃ κ) :
    certificateComplexity (BooleanCube.relabel e f) = certificateComplexity f := by
  unfold certificateComplexity
  rw [show certificateComplexityAt (BooleanCube.relabel e f) = fun x => certificateComplexityAt f (cubeMap e x) from funext (certificateComplexityAt_relabel f e)]
  exact sup_comp_equiv (cubeMap e) (certificateComplexityAt f)

variable [DecidableEq β]

theorem sensitivityAt_relabel (f : (κ → Bool) → β) (e : ι ≃ κ) (x : ι → Bool) :
    sensitivityAt (BooleanCube.relabel e f) x = sensitivityAt f (cubeMap e x) := by
  unfold sensitivityAt
  simp only [BooleanCube.relabel, cubeMap_flip, card_filter]
  exact e.sum_comp fun k => if f (flip k (cubeMap e x)) ≠ f (cubeMap e x) then 1 else 0

theorem sensitivity_relabel (f : (κ → Bool) → β) (e : ι ≃ κ) :
    sensitivity (BooleanCube.relabel e f) = sensitivity f := by
  unfold sensitivity
  rw [show sensitivityAt (BooleanCube.relabel e f) = fun x => sensitivityAt f (cubeMap e x) from funext (sensitivityAt_relabel f e)]
  exact sup_comp_equiv (cubeMap e) (sensitivityAt f)

theorem blockSensitivityAt_relabel_le (f : (κ → Bool) → β) (e : ι ≃ κ) (x : ι → Bool) :
    blockSensitivityAt (BooleanCube.relabel e f) x ≤ blockSensitivityAt f (cubeMap e x) := by
  obtain ⟨F, hF, hcard⟩ := exists_isSensitiveFamily_card_eq (BooleanCube.relabel e f) x
  rw [← hcard, ← card_image_of_injective F (map_injective e.toEmbedding)]
  exact card_le_blockSensitivityAt (isSensitiveFamily_relabel e hF)

theorem blockSensitivityAt_relabel (f : (κ → Bool) → β) (e : ι ≃ κ) (x : ι → Bool) :
    blockSensitivityAt (BooleanCube.relabel e f) x = blockSensitivityAt f (cubeMap e x) := by
  refine le_antisymm (blockSensitivityAt_relabel_le f e x) ?_
  have := blockSensitivityAt_relabel_le (BooleanCube.relabel e f) e.symm (cubeMap e x)
  rwa [relabel_symm_relabel, cubeMap_symm_cubeMap] at this

theorem blockSensitivity_relabel (f : (κ → Bool) → β) (e : ι ≃ κ) :
    blockSensitivity (BooleanCube.relabel e f) = blockSensitivity f := by
  unfold blockSensitivity
  rw [show blockSensitivityAt (BooleanCube.relabel e f) = fun x => blockSensitivityAt f (cubeMap e x) from funext (blockSensitivityAt_relabel f e)]
  exact sup_comp_equiv (cubeMap e) (blockSensitivityAt f)

end Query

end

end TheoremOS.BooleanCube
