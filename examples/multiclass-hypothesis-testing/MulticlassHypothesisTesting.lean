import ArchivedTreeReconstruction

open TheoremOS.Probability
open scoped BigOperators ENNReal

namespace TheoremOS.MulticlassHypothesisTesting

noncomputable section

variable {Label Observation : Type*} [Fintype Label] [Fintype Observation]

/-- Probability of a correct prediction when the labels have a uniform prior. -/
def accuracy (law : Label → PMF Observation) (rule : Observation → Label) : ℝ :=
  (∑ y, (law (rule y) y).toReal) / Fintype.card Label

private theorem accuracy_le_of_likelihood_le
    (law : Label → PMF Observation) (rule best : Observation → Label)
    (h : ∀ y, (law (rule y) y).toReal ≤ (law (best y) y).toReal) :
    accuracy law rule ≤ accuracy law best :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun y _ => h y) (Nat.cast_nonneg _)

private theorem pmfTV_eq_sum_positive (p q : PMF Observation) :
    pmfTV p q = ∑ y, max ((p y).toReal - (q y).toReal) 0 := by
  rw [pmfTV_eq_toReal_tsum_tsub, ENNReal.tsum_toReal_eq
    (fun y => ne_top_of_le_ne_top (p.apply_ne_top y) tsub_le_self), tsum_fintype]
  exact Finset.sum_congr rfl fun y _ => toReal_tsub_pmf p q y

variable [Nonempty Label]

/-- If at most the selected label has likelihood above the mixture at each observation,
the rule's gain over chance equals the archived reconstruction advantage. -/
theorem accuracy_eq_chance_add_advantage (law : Label → PMF Observation)
    (rule : Observation → Label)
    (chosen : ∀ y, (pmfMixture law y).toReal ≤ (law (rule y) y).toReal)
    (other : ∀ y i, i ≠ rule y → (law i y).toReal ≤ (pmfMixture law y).toReal) :
    accuracy law rule = (1 : ℝ) / Fintype.card Label + reconAdvantage law := by
  classical
  have total : ∑ y, (pmfMixture law y).toReal = 1 := by
    simpa only [tsum_fintype] using pmf_tsum_toReal (pmfMixture law)
  have gain : ∑ i, pmfTV (law i) (pmfMixture law) =
      ∑ y, ((law (rule y) y).toReal - (pmfMixture law y).toReal) := by
    calc
      _ = ∑ i, ∑ y, max ((law i y).toReal - (pmfMixture law y).toReal) 0 := by
        simp only [pmfTV_eq_sum_positive]
      _ = ∑ y, ∑ i, max ((law i y).toReal - (pmfMixture law y).toReal) 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_eq_single_of_mem (rule y) (Finset.mem_univ _) (fun i _ hi =>
          max_eq_right (sub_nonpos.mpr (other y i hi)))]
        exact max_eq_left (sub_nonneg.mpr (chosen y))
  rw [accuracy, reconAdvantage, gain, Finset.sum_sub_distrib, total]
  ring

/-- Under the same likelihood conditions, a pairwise total variation distance bounds
the rule's improvement over a uniform guess. -/
theorem chance_add_tv_le_accuracy (law : Label → PMF Observation)
    (rule : Observation → Label)
    (chosen : ∀ y, (pmfMixture law y).toReal ≤ (law (rule y) y).toReal)
    (other : ∀ y i, i ≠ rule y → (law i y).toReal ≤ (pmfMixture law y).toReal)
    (i j : Label) :
    (1 : ℝ) / Fintype.card Label + pmfTV (law i) (law j) / Fintype.card Label ≤
      accuracy law rule := by
  have cardPos : (0 : ℝ) < Fintype.card Label := Nat.cast_pos.mpr Fintype.card_pos
  have pair := pmfTV_le_card_mul_reconAdvantage law i j
  rw [accuracy_eq_chance_add_advantage law rule chosen other]
  apply add_le_add_right
  exact (div_le_iff₀ cardPos).mpr (by simpa only [mul_comm] using pair)

/-- Three labels and three output symbols, with diagonal mass 2/3 and off-diagonal mass 1/6. -/
def symmetricChannel : Fin 3 → PMF (Fin 3) :=
  pottsPMF (lam := 1 / 2) (by norm_num) (by norm_num)

theorem symmetricChannel_apply (i y : Fin 3) :
    (symmetricChannel i y).toReal = if i = y then 2 / 3 else 1 / 6 := by
  rw [symmetricChannel, toReal_pottsPMF_apply, pottsWeight_fin_three]
  split_ifs <;> norm_num

private theorem symmetric_mixture (y : Fin 3) :
    (pmfMixture symmetricChannel y).toReal = (1 : ℝ) / 3 := by
  rw [toReal_pmfMixture_apply, Fin.sum_univ_three]
  fin_cases y <;> norm_num [symmetricChannel_apply]

theorem symmetric_pair_tv : pmfTV (symmetricChannel 0) (symmetricChannel 1) = (1 : ℝ) / 2 := by
  rw [pmfTV, tsum_fintype, Fin.sum_univ_three]
  norm_num [symmetricChannel_apply]

/-- Predicting the observed label attains the maximum accuracy, 2/3. -/
theorem symmetric_channel_optimal :
    accuracy symmetricChannel id = (2 : ℝ) / 3 ∧
      ∀ rule : Fin 3 → Fin 3, accuracy symmetricChannel rule ≤ (2 : ℝ) / 3 := by
  have best : accuracy symmetricChannel id = (2 : ℝ) / 3 := by
    norm_num [accuracy, symmetricChannel_apply, Fin.sum_univ_three]
  refine ⟨best, fun rule => ?_⟩
  rw [← best]
  apply accuracy_le_of_likelihood_le
  intro y
  simp only [symmetricChannel_apply, id_eq, ite_true]
  split_ifs <;> norm_num

/-- The archive's pairwise bound certifies accuracy at least 1/2 for this decoder. -/
theorem symmetric_archive_bound : (1 : ℝ) / 2 ≤ accuracy symmetricChannel id := by
  have lower := chance_add_tv_le_accuracy symmetricChannel id
    (fun y => by rw [symmetric_mixture]; simp [symmetricChannel_apply]; norm_num)
    (fun y i hi => by
      change i ≠ y at hi
      rw [symmetric_mixture, symmetricChannel_apply, ite_eq_right hi]
      norm_num)
    0 1
  rw [symmetric_pair_tv] at lower
  norm_num at lower
  exact lower

private def headsProbability (i : Fin 3) : ℝ :=
  if i = 0 then 3 / 4 else if i = 1 then 1 / 4 else 1 / 2

private def binaryWeight (i : Fin 3) (y : Bool) : ℝ :=
  if y then headsProbability i else 1 - headsProbability i

private theorem binaryWeight_nonneg (i : Fin 3) (y : Bool) : 0 ≤ binaryWeight i y := by
  fin_cases i <;> cases y <;> norm_num [binaryWeight, headsProbability]

/-- Three uniform labels with respective probabilities 3/4, 1/4 and 1/2 of observing true. -/
def sharpChannel (i : Fin 3) : PMF Bool :=
  PMF.ofFintype (fun y => ENNReal.ofReal (binaryWeight i y)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => binaryWeight_nonneg i y),
      Fintype.sum_bool]
    change ENNReal.ofReal (headsProbability i + (1 - headsProbability i)) = 1
    rw [show headsProbability i + (1 - headsProbability i) = 1 by ring, ENNReal.ofReal_one])

private theorem sharpChannel_apply (i : Fin 3) (y : Bool) :
    (sharpChannel i y).toReal = binaryWeight i y := by
  rw [sharpChannel, PMF.ofFintype_apply, ENNReal.toReal_ofReal (binaryWeight_nonneg i y)]

private theorem sharp_mixture (y : Bool) : (pmfMixture sharpChannel y).toReal = (1 : ℝ) / 2 := by
  rw [toReal_pmfMixture_apply, Fin.sum_univ_three]
  cases y <;> norm_num [sharpChannel_apply, binaryWeight, headsProbability]

/-- The maximum-likelihood decision for the two outputs. -/
def sharpRule (y : Bool) : Fin 3 := if y then 0 else 1

/-- Both the archive's pairwise total variation bound and the accuracy bound are exact
for the three labels with two outputs. -/
theorem sharp_experiment :
    pmfTV (sharpChannel 0) (sharpChannel 1) = (1 : ℝ) / 2 ∧
      pmfTV (sharpChannel 0) (sharpChannel 1) = 3 * reconAdvantage sharpChannel ∧
      accuracy sharpChannel sharpRule =
        (1 : ℝ) / 3 + pmfTV (sharpChannel 0) (sharpChannel 1) / 3 ∧
      accuracy sharpChannel sharpRule = (1 : ℝ) / 2 ∧
      ∀ rule : Bool → Fin 3, accuracy sharpChannel rule ≤ (1 : ℝ) / 2 := by
  have pair : pmfTV (sharpChannel 0) (sharpChannel 1) = (1 : ℝ) / 2 := by
    rw [pmfTV, tsum_fintype, Fintype.sum_bool]
    norm_num [sharpChannel_apply, binaryWeight, headsProbability]
  have chosen (y : Bool) : (pmfMixture sharpChannel y).toReal ≤
      (sharpChannel (sharpRule y) y).toReal := by
    rw [sharp_mixture]
    cases y <;> norm_num [sharpRule, sharpChannel_apply, binaryWeight, headsProbability]
  have other (y : Bool) (i : Fin 3) (hi : i ≠ sharpRule y) :
      (sharpChannel i y).toReal ≤ (pmfMixture sharpChannel y).toReal := by
    rw [sharp_mixture]
    cases y <;> fin_cases i <;>
      first | contradiction | norm_num [sharpRule, sharpChannel_apply, binaryWeight, headsProbability]
  have best : accuracy sharpChannel sharpRule = (1 : ℝ) / 2 := by
    norm_num [accuracy, Fintype.sum_bool, sharpRule, sharpChannel_apply,
      binaryWeight, headsProbability]
  have gain := accuracy_eq_chance_add_advantage sharpChannel sharpRule chosen other
  rw [best] at gain
  refine ⟨pair, ?_, ?_, best, fun rule => ?_⟩
  · norm_num at gain
    rw [pair]
    linarith
  · rw [best, pair]
    norm_num
  · rw [← best]
    apply accuracy_le_of_likelihood_le
    intro y
    by_cases heq : rule y = sharpRule y
    · rw [heq]
    · exact (other y (rule y) heq).trans (chosen y)

#print axioms accuracy_eq_chance_add_advantage
#print axioms chance_add_tv_le_accuracy
#print axioms symmetric_channel_optimal
#print axioms symmetric_archive_bound
#print axioms sharp_experiment

end

end TheoremOS.MulticlassHypothesisTesting
