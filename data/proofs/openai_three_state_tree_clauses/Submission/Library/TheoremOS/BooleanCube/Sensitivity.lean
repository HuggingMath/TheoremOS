import Submission.Library.TheoremOS.BooleanCube.Influence

/-!
# Sensitivity, block sensitivity and certificate complexity

For `f : (ι → Bool) → β` and a point `x`: block flips `flipSet B x`; sensitivity `s(f, x)`
(coordinates whose flip changes `f x`); block sensitivity `bs(f, x)` (the largest number of
pairwise disjoint blocks whose flips each change `f x`); certificate complexity `C(f, x)` (the
fewest coordinates whose values at `x` force `f x`). Proved: `s(f, x) ≤ bs(f, x) ≤ C(f, x) ≤ |ι|`,
every certificate meets every sensitive block, minimal sensitive blocks have size at most `s(f)`,
Nisan's bound `C(f, x) ≤ s(f) · bs(f, x)`, the global versions `s f ≤ bs f ≤ C f ≤ s f · bs f`,
and invariance of `s`, `bs` under post-composition with an injective map.

Sources: N. Nisan, "CREW PRAMs and decision trees", SIAM J. Comput. 20 (1991); H. Buhrman and
R. de Wolf, "Complexity measures and decision tree complexity: a survey", Theoret. Comput. Sci.
288 (2002), §2–3. Textbook material.

Bridges: `flipSet B x i = if i ∈ B then !(x i) else x i` (`flipSet_apply`, `flipSet_eq_ite` for an
arbitrary decidability instance); `flipSet {i} x = flip i x`. `sensitivityAt f x` counts
`i` with `f (flipSet {i} x) ≠ f x` (`sensitivityAt_eq_card_flipSet_singleton`).
`IsSensitiveFamily f x F` is "pairwise disjoint, each block nonempty and flipping it changes `f x`"
(`isSensitiveFamily_iff`), and a sup of `if (that) then F.card else 0` over all families is
`blockSensitivityAt` (`blockSensitivityAt_eq_sup`). `Query.sensitivityAt` for real-valued `f` is
the Influence-module `BooleanCube.sensitivityAt` (`sensitivityAt_eq_booleanCube`).
-/

namespace TheoremOS.BooleanCube

open Finset
open scoped BigOperators

variable {ι : Type*}

section Flip

variable [DecidableEq ι]

/-- Flip the coordinates in `B`. -/
def flipSet (B : Finset ι) (x : ι → Bool) : ι → Bool := fun i => if i ∈ B then !(x i) else x i

lemma flipSet_apply (B : Finset ι) (x : ι → Bool) (i : ι) :
    flipSet B x i = if i ∈ B then !(x i) else x i := rfl

lemma flipSet_eq_ite (B : Finset ι) (x : ι → Bool) [∀ i, Decidable (i ∈ B)] :
    flipSet B x = fun i => if i ∈ B then !(x i) else x i := by
  funext i; unfold flipSet; split_ifs <;> rfl

@[simp] lemma flipSet_empty (x : ι → Bool) : flipSet ∅ x = x := by funext i; simp [flipSet]

lemma flipSet_singleton (i : ι) (x : ι → Bool) : flipSet {i} x = flip i x := by
  funext j
  by_cases h : j = i
  · subst h; simp [flipSet]
  · simp [flipSet, h, flip_apply_of_ne h]

@[simp] lemma flipSet_flipSet (B : Finset ι) (x : ι → Bool) : flipSet B (flipSet B x) = x := by
  funext i; unfold flipSet; split_ifs <;> simp

lemma flipSet_apply_of_notMem {B : Finset ι} {i : ι} (h : i ∉ B) (x : ι → Bool) : flipSet B x i = x i := by
  simp [flipSet, h]

lemma flipSet_apply_of_mem {B : Finset ι} {i : ι} (h : i ∈ B) (x : ι → Bool) : flipSet B x i = !(x i) := by
  simp [flipSet, h]

lemma flipSet_erase {B : Finset ι} {j : ι} (hj : j ∈ B) (x : ι → Bool) :
    flipSet (B.erase j) x = flip j (flipSet B x) := by
  funext i
  by_cases h : i = j
  · subst h; simp [flipSet, hj]
  · rw [flip_apply_of_ne h]; simp [flipSet, h]

/-- The set of coordinates where `x` and `y` differ flips `x` to `y`. -/
lemma flipSet_filter_ne (x y : ι → Bool) [Fintype ι] : flipSet (univ.filter fun i => x i ≠ y i) x = y := by
  funext i
  by_cases h : x i = y i <;> simp [flipSet, h]
  cases hx : x i <;> cases hy : y i <;> simp_all

end Flip

namespace Query

variable {β : Type*}

/-- `C` is a certificate for `f` at `x`: agreeing with `x` on `C` forces the value `f x`. -/
def IsCertificate (f : (ι → Bool) → β) (x : ι → Bool) (C : Finset ι) : Prop :=
  ∀ y : ι → Bool, (∀ i ∈ C, y i = x i) → f y = f x

lemma isCertificate_univ [Fintype ι] (f : (ι → Bool) → β) (x : ι → Bool) : IsCertificate f x univ := by
  intro y hy
  have : y = x := funext fun i => hy i (mem_univ i)
  rw [this]

/-- `C(f, x)`: the smallest size of a certificate at `x`. -/
noncomputable def certificateComplexityAt (f : (ι → Bool) → β) (x : ι → Bool) : ℕ :=
  sInf {k | ∃ C, IsCertificate f x C ∧ C.card = k}

lemma certificateComplexityAt_le_card {f : (ι → Bool) → β} {x : ι → Bool} {C : Finset ι}
    (hC : IsCertificate f x C) : certificateComplexityAt f x ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

lemma exists_isCertificate_card_eq [Fintype ι] (f : (ι → Bool) → β) (x : ι → Bool) :
    ∃ C, IsCertificate f x C ∧ C.card = certificateComplexityAt f x := by
  have h : ({k | ∃ C, IsCertificate f x C ∧ C.card = k} : Set ℕ).Nonempty :=
    ⟨_, Set.mem_ofPred.2 ⟨univ, isCertificate_univ f x, rfl⟩⟩
  exact Nat.sInf_mem h

theorem certificateComplexityAt_le_card_univ [Fintype ι] (f : (ι → Bool) → β) (x : ι → Bool) :
    certificateComplexityAt f x ≤ Fintype.card ι :=
  (certificateComplexityAt_le_card (isCertificate_univ f x)).trans_eq card_univ

variable [DecidableEq ι]

/-- A family of pairwise disjoint blocks each of whose flips changes `f x`. -/
def IsSensitiveFamily (f : (ι → Bool) → β) (x : ι → Bool) (F : Finset (Finset ι)) : Prop :=
  (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ ∀ B ∈ F, f (flipSet B x) ≠ f x

lemma isSensitiveFamily_empty (f : (ι → Bool) → β) (x : ι → Bool) : IsSensitiveFamily f x ∅ := by
  simp [IsSensitiveFamily]

lemma nonempty_of_sensitive {f : (ι → Bool) → β} {x : ι → Bool} {B : Finset ι}
    (h : f (flipSet B x) ≠ f x) : B.Nonempty := by
  rw [nonempty_iff_ne_empty]; rintro rfl; simp at h

lemma isSensitiveFamily_iff (f : (ι → Bool) → β) (x : ι → Bool) (F : Finset (Finset ι)) :
    IsSensitiveFamily f x F ↔
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ ∀ B ∈ F, B.Nonempty ∧ f (flipSet B x) ≠ f x :=
  and_congr Iff.rfl ⟨fun h B hB => ⟨nonempty_of_sensitive (h B hB), h B hB⟩, fun h B hB => (h B hB).2⟩

lemma isSensitiveFamily_comp {γ : Type*} {g : β → γ} (hg : Function.Injective g) (f : (ι → Bool) → β)
    (x : ι → Bool) (F : Finset (Finset ι)) :
    IsSensitiveFamily (fun y => g (f y)) x F ↔ IsSensitiveFamily f x F := by
  simp only [IsSensitiveFamily, hg.ne_iff]

/-- A certificate at `x` meets every block whose flip changes `f x`. -/
lemma IsCertificate.not_disjoint {f : (ι → Bool) → β} {x : ι → Bool} {C B : Finset ι}
    (hC : IsCertificate f x C) (hB : f (flipSet B x) ≠ f x) : ¬Disjoint C B := fun hdis =>
  hB (hC _ fun _ hi => flipSet_apply_of_notMem (disjoint_left.1 hdis hi) x)

/-- `B` is a minimal sensitive block at `x`. -/
def IsMinimalSensitive (f : (ι → Bool) → β) (x : ι → Bool) (B : Finset ι) : Prop :=
  f (flipSet B x) ≠ f x ∧ ∀ A ⊂ B, f (flipSet A x) = f x

lemma exists_minimalSensitive_subset {f : (ι → Bool) → β} {x : ι → Bool} {B : Finset ι}
    (hB : f (flipSet B x) ≠ f x) : ∃ M ⊆ B, IsMinimalSensitive f x M := by
  classical
  obtain ⟨M, hM, hmin⟩ := exists_min_image (B.powerset.filter fun A => f (flipSet A x) ≠ f x) card
    ⟨B, mem_filter.2 ⟨mem_powerset_self B, hB⟩⟩
  obtain ⟨hMB, hMs⟩ := mem_filter.1 hM
  refine ⟨M, mem_powerset.1 hMB, hMs, fun A hA => ?_⟩
  by_contra hne
  have := hmin A (mem_filter.2 ⟨mem_powerset.2 (hA.subset.trans (mem_powerset.1 hMB)), hne⟩)
  exact absurd (card_lt_card hA) (not_lt.2 this)

variable [Fintype ι]

/-- `C(f) = max_x C(f, x)`. -/
noncomputable def certificateComplexity (f : (ι → Bool) → β) : ℕ := univ.sup (certificateComplexityAt f)

lemma certificateComplexityAt_le_certificateComplexity (f : (ι → Bool) → β) (x : ι → Bool) :
    certificateComplexityAt f x ≤ certificateComplexity f :=
  le_sup (f := certificateComplexityAt f) (mem_univ x)

variable [DecidableEq β]

instance (f : (ι → Bool) → β) (x : ι → Bool) : DecidablePred (IsSensitiveFamily f x) := fun F => by
  unfold IsSensitiveFamily; infer_instance

/-- `s(f, x)`: the number of coordinates whose flip changes `f x`. -/
def sensitivityAt (f : (ι → Bool) → β) (x : ι → Bool) : ℕ := (univ.filter fun i => f (flip i x) ≠ f x).card

/-- `s(f) = max_x s(f, x)`. -/
def sensitivity (f : (ι → Bool) → β) : ℕ := univ.sup (sensitivityAt f)

lemma sensitivityAt_le_sensitivity (f : (ι → Bool) → β) (x : ι → Bool) : sensitivityAt f x ≤ sensitivity f :=
  le_sup (f := sensitivityAt f) (mem_univ x)

lemma sensitivityAt_eq_card_flipSet_singleton (f : (ι → Bool) → β) (x : ι → Bool) :
    sensitivityAt f x = (univ.filter fun i => f (flipSet {i} x) ≠ f x).card := by
  simp only [sensitivityAt, flipSet_singleton]

lemma sensitivityAt_eq_booleanCube (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    sensitivityAt f x = BooleanCube.sensitivityAt f x := by
  unfold sensitivityAt BooleanCube.sensitivityAt
  simp only [ne_comm]

/-- `bs(f, x)`: the largest size of a sensitive family. -/
def blockSensitivityAt (f : (ι → Bool) → β) (x : ι → Bool) : ℕ :=
  (univ.filter (IsSensitiveFamily f x)).sup card

/-- `bs(f) = max_x bs(f, x)`. -/
def blockSensitivity (f : (ι → Bool) → β) : ℕ := univ.sup (blockSensitivityAt f)

lemma blockSensitivityAt_le_blockSensitivity (f : (ι → Bool) → β) (x : ι → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f :=
  le_sup (f := blockSensitivityAt f) (mem_univ x)

lemma card_le_blockSensitivityAt {f : (ι → Bool) → β} {x : ι → Bool} {F : Finset (Finset ι)}
    (hF : IsSensitiveFamily f x F) : F.card ≤ blockSensitivityAt f x :=
  le_sup (f := card) (mem_filter.2 ⟨mem_univ F, hF⟩)

lemma exists_isSensitiveFamily_card_eq (f : (ι → Bool) → β) (x : ι → Bool) :
    ∃ F, IsSensitiveFamily f x F ∧ F.card = blockSensitivityAt f x := by
  obtain ⟨F, hF, h⟩ := exists_mem_eq_sup (univ.filter (IsSensitiveFamily f x))
    ⟨∅, mem_filter.2 ⟨mem_univ _, isSensitiveFamily_empty f x⟩⟩ card
  exact ⟨F, (mem_filter.1 hF).2, h.symm⟩

/-- Any expression that bounds every sensitive family and is attained by one is `bs(f, x)`. -/
theorem blockSensitivityAt_eq_sup (f : (ι → Bool) → β) (x : ι → Bool) (g : Finset (Finset ι) → ℕ)
    (hg : ∀ F, g F = if IsSensitiveFamily f x F then F.card else 0) :
    univ.sup g = blockSensitivityAt f x := by
  apply le_antisymm
  · refine Finset.sup_le fun F _ => ?_
    rw [hg]; split_ifs with h
    · exact card_le_blockSensitivityAt h
    · exact Nat.zero_le _
  · obtain ⟨F, hF, hcard⟩ := exists_isSensitiveFamily_card_eq f x
    rw [← hcard]
    refine le_trans (le_of_eq ?_) (le_sup (f := g) (mem_univ F))
    simp only [hg, hF, ↓reduceIte]

/-- `bs(f, x) ≤ |ι|`. -/
theorem blockSensitivityAt_le_card (f : (ι → Bool) → β) (x : ι → Bool) :
    blockSensitivityAt f x ≤ Fintype.card ι := by
  obtain ⟨F, hF, hcard⟩ := exists_isSensitiveFamily_card_eq f x
  rw [← hcard]
  calc F.card = ∑ _B ∈ F, 1 := by rw [card_eq_sum_ones]
    _ ≤ ∑ B ∈ F, B.card := sum_le_sum fun B hB => (nonempty_of_sensitive (hF.2 B hB)).card_pos
    _ = (F.biUnion id).card := (card_biUnion fun A hA B hB hAB => hF.1 A hA B hB hAB).symm
    _ ≤ Fintype.card ι := card_le_univ _

/-- `s(f, x) ≤ bs(f, x)`: singletons of sensitive coordinates form a sensitive family. -/
theorem sensitivityAt_le_blockSensitivityAt (f : (ι → Bool) → β) (x : ι → Bool) :
    sensitivityAt f x ≤ blockSensitivityAt f x := by
  have hF : IsSensitiveFamily f x ((univ.filter fun i => f (flip i x) ≠ f x).image fun i => {i}) := by
    refine ⟨?_, ?_⟩
    · simp only [mem_image]
      rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hij
      exact disjoint_singleton.2 fun h => hij (h ▸ rfl)
    · simp only [mem_image, mem_filter, mem_univ, true_and]
      rintro _ ⟨i, hi, rfl⟩
      rwa [flipSet_singleton]
  have := card_le_blockSensitivityAt hF
  rwa [card_image_of_injective _ singleton_injective] at this

theorem sensitivity_le_blockSensitivity (f : (ι → Bool) → β) : sensitivity f ≤ blockSensitivity f :=
  sup_mono_fun fun x _ => sensitivityAt_le_blockSensitivityAt f x

/-- `bs(f, x) ≤ C(f, x)`. -/
theorem blockSensitivityAt_le_certificateComplexityAt (f : (ι → Bool) → β) (x : ι → Bool) :
    blockSensitivityAt f x ≤ certificateComplexityAt f x := by
  obtain ⟨F, hF, hFcard⟩ := exists_isSensitiveFamily_card_eq f x
  obtain ⟨C, hC, hCcard⟩ := exists_isCertificate_card_eq f x
  rw [← hFcard, ← hCcard]
  calc F.card = ∑ _B ∈ F, 1 := by rw [card_eq_sum_ones]
    _ ≤ ∑ B ∈ F, (C ∩ B).card := sum_le_sum fun B hB =>
        card_pos.2 (not_disjoint_iff_nonempty_inter.1 (hC.not_disjoint (hF.2 B hB)))
    _ = (F.biUnion fun B => C ∩ B).card := (card_biUnion fun A hA B hB hAB =>
        (hF.1 A hA B hB hAB).mono inter_subset_right inter_subset_right).symm
    _ ≤ C.card := card_le_card (biUnion_subset.2 fun _ _ => inter_subset_left)

theorem blockSensitivity_le_certificateComplexity (f : (ι → Bool) → β) :
    blockSensitivity f ≤ certificateComplexity f :=
  sup_mono_fun fun x _ => blockSensitivityAt_le_certificateComplexityAt f x

/-- Every coordinate of a minimal sensitive block `B` is sensitive at `flipSet B x`, so
`|B| ≤ s(f)`. -/
theorem IsMinimalSensitive.card_le_sensitivity {f : (ι → Bool) → β} {x : ι → Bool} {B : Finset ι}
    (hB : IsMinimalSensitive f x B) : B.card ≤ sensitivity f := by
  have hsub : B ⊆ univ.filter fun j => f (flip j (flipSet B x)) ≠ f (flipSet B x) := by
    intro j hj
    refine mem_filter.2 ⟨mem_univ j, ?_⟩
    rw [← flipSet_erase hj, hB.2 _ (erase_ssubset hj)]
    exact fun h => hB.1 h.symm
  exact (card_le_card hsub).trans (sensitivityAt_le_sensitivity f _)

/-- Nisan: `C(f, x) ≤ s(f) · bs(f, x)`. A largest disjoint family of minimal sensitive blocks
covers a certificate. -/
theorem certificateComplexityAt_le_mul (f : (ι → Bool) → β) (x : ι → Bool) :
    certificateComplexityAt f x ≤ blockSensitivityAt f x * sensitivity f := by
  classical
  let P : Finset (Finset ι) → Prop := fun F =>
    (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ ∀ B ∈ F, IsMinimalSensitive f x B
  obtain ⟨F, hFmem, hFmax⟩ := exists_max_image (univ.filter P) card
    ⟨∅, mem_filter.2 ⟨mem_univ _, by simp [P]⟩⟩
  have hF : P F := (mem_filter.1 hFmem).2
  have hFs : IsSensitiveFamily f x F := ⟨hF.1, fun B hB => (hF.2 B hB).1⟩
  have hcert : IsCertificate f x (F.biUnion id) := by
    intro y hy
    by_contra hne
    have hD : flipSet (univ.filter fun i => x i ≠ y i) x = y := flipSet_filter_ne x y
    obtain ⟨M, hMD, hM⟩ := exists_minimalSensitive_subset (B := univ.filter fun i => x i ≠ y i)
      (by rw [hD]; exact hne)
    have hdis : ∀ B ∈ F, Disjoint M B := fun B hB => disjoint_left.2 fun i hiM hiB =>
      (mem_filter.1 (hMD hiM)).2 (hy i (mem_biUnion.2 ⟨B, hB, hiB⟩)).symm
    have hMF : M ∉ F := fun h => by
      have := hdis M h
      rw [disjoint_self_iff_empty] at this
      exact (nonempty_of_sensitive hM.1).ne_empty this
    have hP : P (insert M F) := by
      refine ⟨?_, ?_⟩
      · intro A hA B hB hAB
        rcases mem_insert.1 hA with rfl | hA' <;> rcases mem_insert.1 hB with rfl | hB'
        · exact absurd rfl hAB
        · exact hdis B hB'
        · exact (hdis A hA').symm
        · exact hF.1 A hA' B hB' hAB
      · intro B hB
        rcases mem_insert.1 hB with rfl | hB
        · exact hM
        · exact hF.2 B hB
    have := hFmax _ (mem_filter.2 ⟨mem_univ _, hP⟩)
    rw [card_insert_of_notMem hMF] at this
    omega
  calc certificateComplexityAt f x ≤ (F.biUnion id).card := certificateComplexityAt_le_card hcert
    _ ≤ ∑ B ∈ F, B.card := card_biUnion_le
    _ ≤ ∑ _B ∈ F, sensitivity f := sum_le_sum fun B hB => (hF.2 B hB).card_le_sensitivity
    _ = F.card * sensitivity f := by rw [sum_const, smul_eq_mul]
    _ ≤ blockSensitivityAt f x * sensitivity f := Nat.mul_le_mul_right _ (card_le_blockSensitivityAt hFs)

theorem certificateComplexity_le_mul (f : (ι → Bool) → β) :
    certificateComplexity f ≤ blockSensitivity f * sensitivity f :=
  Finset.sup_le fun x _ => (certificateComplexityAt_le_mul f x).trans
    (Nat.mul_le_mul_right _ (blockSensitivityAt_le_blockSensitivity f x))

section Comp

variable {γ : Type*} [DecidableEq γ]

lemma sensitivityAt_comp {g : β → γ} (hg : Function.Injective g) (f : (ι → Bool) → β) (x : ι → Bool) :
    sensitivityAt (fun y => g (f y)) x = sensitivityAt f x := by
  simp only [sensitivityAt, hg.ne_iff]

lemma sensitivity_comp {g : β → γ} (hg : Function.Injective g) (f : (ι → Bool) → β) :
    sensitivity (fun y => g (f y)) = sensitivity f := by
  unfold sensitivity; congr 1; funext x; exact sensitivityAt_comp hg f x

lemma blockSensitivityAt_comp {g : β → γ} (hg : Function.Injective g) (f : (ι → Bool) → β)
    (x : ι → Bool) : blockSensitivityAt (fun y => g (f y)) x = blockSensitivityAt f x := by
  unfold blockSensitivityAt
  congr 1
  ext F
  simp only [mem_filter, mem_univ, true_and, isSensitiveFamily_comp hg]

lemma blockSensitivity_comp {g : β → γ} (hg : Function.Injective g) (f : (ι → Bool) → β) :
    blockSensitivity (fun y => g (f y)) = blockSensitivity f := by
  unfold blockSensitivity; congr 1; funext x; exact blockSensitivityAt_comp hg f x

end Comp

end Query

end TheoremOS.BooleanCube
