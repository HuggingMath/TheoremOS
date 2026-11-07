import Submission.Library.Auto.ThreeStateChannelSpectrum
import Submission.Library.TheoremOS.Probability.TreeReconstruction
import Mathlib

namespace OAI

namespace ThreeState

abbrev Spin := Fin 3

 
def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

 
noncomputable def channel (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

 

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

noncomputable def leafSum (phi : Spin → ℝ) : (n : ℕ) → Observation n → ℝ
  | 0 => phi
  | n + 1 => fun s => (s.map (leafSum phi n)).sum
theorem leafSum_zero (phi : Spin → ℝ) (i : Spin) :
    leafSum phi 0 i = phi i := rfl
theorem leafSum_succ (phi : Spin → ℝ) (n : ℕ) (s : Multiset (Observation n)) :
    leafSum phi (n + 1) s = (s.map (leafSum phi n)).sum := rfl
theorem channel_nonneg {lam : ℝ} (h : Admissible lam) (i j : Spin) :
    0 ≤ channel lam i j := by
  unfold channel
  split_ifs
  · dsimp [Admissible] at h
    linarith [h.1]
  · dsimp [Admissible] at h
    linarith [h.2]

theorem channel_sum (lam : ℝ) (i : Spin) : ∑ j, channel lam i j = 1 := by
  fin_cases i <;> simp [channel, Fin.sum_univ_succ] <;> ring

theorem channel_col_sum (lam : ℝ) (j : Spin) : ∑ i : Spin, channel lam i j = 1 := by
  fin_cases j <;> simp [channel, Fin.sum_univ_succ] <;> ring
theorem channel_eigen (lam : ℝ) (phi : Spin → ℝ) (hphi : ∑ j : Spin, phi j = 0) :
    ∀ i : Spin, ∑ j : Spin, channel lam i j * phi j = lam * phi i := by
  intro i
  have hterm : ∀ j : Spin, channel lam i j * phi j =
      (1 - lam) / 3 * phi j + (if i = j then lam * phi j else 0) := by
    intro j
    unfold channel
    split_ifs <;> ring
  calc ∑ j : Spin, channel lam i j * phi j
      = ∑ j : Spin, ((1 - lam) / 3 * phi j + (if i = j then lam * phi j else 0)) :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = (1 - lam) / 3 * (∑ j : Spin, phi j)
          + ∑ j : Spin, (if i = j then lam * phi j else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = lam * phi i := by
        rw [hphi, mul_zero, zero_add]
        simp [Finset.sum_ite_eq]
noncomputable def channelPMF (lam : ℝ) (h : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j => ENNReal.ofReal (channel lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => channel_nonneg h i j)]
    simp [channel_sum])

 
theorem toReal_channelPMF (lam : ℝ) (h : Admissible lam) (i j : Spin) :
    (channelPMF lam h i j).toReal = channel lam i j := by
  exact ENNReal.toReal_ofReal (channel_nonneg h i j)
noncomputable def iidList {α : Type*} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun a => (iidList p n).map (List.cons a)

 

noncomputable def observedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    (n : ℕ) → Spin → PMF (Observation n)
  | 0, i => PMF.pure i
  | n + 1, i => offspring.bind fun k =>
      (iidList ((channelPMF lam h i).bind (observedLaw offspring lam h n)) k).map
        (fun xs : List (Observation n) => (xs : Multiset (Observation n)))

noncomputable def uniformSpin : PMF Spin := PMF.ofFintype (fun _ => 1 / 3) (by
  simp
  exact ENNReal.mul_inv_cancel (by norm_num) (by finiteness))

 
noncomputable def marginal {α : Type*} (law : Spin → PMF α) : PMF α :=
  uniformSpin.bind law

 
noncomputable def posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) : ℝ :=
  if marginal law y = 0 then 1 / 3
  else (law i y).toReal / (3 * (marginal law y).toReal)

 

noncomputable def advantage {α : Type*} (law : Spin → PMF α) : ℝ :=
  ∑' y, (marginal law y).toReal *
    ((∑ i : Spin, |posterior law y i - 1 / 3|) / 2)

noncomputable def regularLaw (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) :=
  observedLaw (PMF.pure b) lam h n

 
noncomputable def poissonOffspring (d : ℝ) (hd : 0 ≤ d) : PMF ℕ := by
  refine ⟨fun k => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)), ?_⟩
  apply ENNReal.hasSum_coe.2
  have hsum : HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / (k.factorial : ℝ)) 1 :=
    ProbabilityTheory.hasSum_one_poissonMeasure ⟨d, hd⟩
  simpa using hsum.toNNReal (fun k => by positivity)

noncomputable def poissonLaw (d : ℝ) (hd : 0 ≤ d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) :=
  observedLaw (poissonOffspring d hd) lam h n

noncomputable def regularAdvantage (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (regularLaw b lam h n)

noncomputable def poissonAdvantage (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (n : ℕ) : ℝ :=
  advantage (poissonLaw d (le_trans (by norm_num) hd.le) lam h n)

 
def Reconstructs (a : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ Filter.Tendsto a Filter.atTop (nhds L)

theorem isBroadcastLaw_observedLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    TheoremOS.Probability.IsBroadcastLaw (channelPMF lam h) offspring (fun i : Spin => i)
      (fun _ s => s) (observedLaw offspring lam h) := by
  refine ⟨fun i => rfl, fun n i => ?_⟩
  simp only [observedLaw]
  rw [TheoremOS.Probability.iidList_eq_of_rec iidList (fun _ => rfl) (fun _ _ => rfl)]
theorem observedLaw_isBroadcastLaw (offspring : PMF ℕ) (lam : ℝ) (h : Admissible lam) :
    TheoremOS.Probability.IsBroadcastLaw (channelPMF lam h) offspring (fun i : Spin => i)
      (fun _ s => s) (observedLaw offspring lam h) :=
  isBroadcastLaw_observedLaw offspring lam h
theorem uniformSpin_apply (i : Spin) :
    uniformSpin i = (Fintype.card Spin : ENNReal)⁻¹ := by
  simp [uniformSpin, Fintype.card_fin]
theorem advantage_eq_reconAdvantage {α : Type*} (law : Spin → PMF α) :
    advantage law = TheoremOS.Probability.reconAdvantage law := by
  have hmix : marginal law = TheoremOS.Probability.pmfMixture law := by
    simp only [marginal]
    exact TheoremOS.Probability.bind_eq_pmfMixture uniformSpin uniformSpin_apply law
  unfold advantage posterior
  rw [hmix]
  exact TheoremOS.Probability.tsum_mul_posterior_ite_eq_reconAdvantage law (1 / 3) (by norm_num)
noncomputable def census : (n : ℕ) → Observation n → ENNReal
  | 0 => fun i => if (show Spin from i) = (1 : Spin) then 1 else 0
  | n + 1 => fun s => (s.map (census n)).sum
theorem census_succ (n : ℕ) (s : Multiset (Observation n)) :
    census (n + 1) s = (s.map (census n)).sum := rfl
noncomputable def eSpin : Spin → ℝ :=
  fun i => (if i = (1 : Spin) then (1 : ℝ) else 0) - 1 / 3
theorem indicator_eq_eSpin (i : Spin) :
    (if i = (1 : Spin) then (1 : ℝ) else 0) = 1 / 3 + eSpin i := by
  unfold eSpin; ring
theorem channel_mul_eSpin (lam : ℝ) (i : Spin) :
    ∑ j, channel lam i j * eSpin j = lam * eSpin i := by
  fin_cases i <;> (simp [channel, eSpin, Fin.sum_univ_three]; ring)
theorem sum_eSpin : ∑ i, eSpin i = 0 := by
  simp [eSpin, Fin.sum_univ_three]
theorem eSpin_one_sub_zero : eSpin (1 : Spin) - eSpin (0 : Spin) = 1 := by
  simp [eSpin]
theorem eSpin_sq_le (i : Spin) : eSpin i ^ 2 ≤ (4 : ℝ) / 9 := by
  fin_cases i <;> norm_num [eSpin]
noncomputable def regM (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, regularLaw b lam h n i o * census n o
noncomputable def regA (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, regularLaw b lam h n i o * (census n o * census n o)
theorem channelPMF_tsum (lam : ℝ) (h : Admissible lam) (i : Spin) :
    (∑ j : Spin, channelPMF lam h i j) = 1 := by
  rw [← tsum_fintype (L := SummationFilter.unconditional Spin)]
  simpa using (channelPMF lam h i).tsum_coe
theorem regM_zero (b : ℕ) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    regM b lam h 0 i = (if i = (1 : Spin) then (1 : ENNReal) else 0) := by
  unfold regM regularLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * census 0 o) = _
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [census]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem regM_rec (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regM b lam h (n + 1) i =
      (b : ENNReal) * ∑ j : Spin, channelPMF lam h i j * regM b lam h n j := by
  unfold regM
  have hb := (isBroadcastLaw_observedLaw (PMF.pure b) lam h).tsum_mul_census
    (O := Observation) (K := channelPMF lam h) (N := PMF.pure b)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (PMF.pure b) lam h) census (fun n s => census_succ n s) n i
  simpa [regularLaw, TheoremOS.Probability.tsum_pure_mul_natCast] using hb
theorem regM_bound (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regM b lam h n i ≤ (b ^ n : ENNReal) := by
  induction n generalizing i with
  | zero =>
      rw [regM_zero]
      split_ifs <;> simp
  | succ n ih =>
      rw [regM_rec]
      calc
        (b : ENNReal) * ∑ j : Spin, channelPMF lam h i j * regM b lam h n j
            ≤ (b : ENNReal) * ∑ j : Spin, channelPMF lam h i j * (b ^ n : ENNReal) := by
              gcongr with j
              exact ih j
        _ = (b : ENNReal) * ((b ^ n : ENNReal) * ∑ j : Spin, channelPMF lam h i j) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (b ^ (n + 1) : ENNReal) := by
              rw [channelPMF_tsum, mul_one, pow_succ]
              ring
theorem regM_ne_top (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regM b lam h n i ≠ ⊤ :=
  ne_top_of_le_ne_top (by simpa [Nat.cast_pow] using ENNReal.natCast_ne_top (b ^ n))
    (regM_bound b lam h n i)
theorem regA_rec (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regA b lam h (n + 1) i =
      (b : ENNReal) * ∑ j : Spin, channelPMF lam h i j * regA b lam h n j +
        ((b * (b - 1) : ℕ) : ENNReal) *
          ((∑ j : Spin, channelPMF lam h i j * regM b lam h n j) *
           (∑ j : Spin, channelPMF lam h i j * regM b lam h n j)) := by
  unfold regA regM
  have hb := (isBroadcastLaw_observedLaw (PMF.pure b) lam h).tsum_mul_census_mul_census
    (O := Observation) (K := channelPMF lam h) (N := PMF.pure b)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (PMF.pure b) lam h) census census
    (fun n s => census_succ n s) (fun n s => census_succ n s) n i
  simpa [regularLaw, TheoremOS.Probability.tsum_pure_mul_natCast] using hb
theorem regA_zero (b : ℕ) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    regA b lam h 0 i = (if i = (1 : Spin) then (1 : ENNReal) else 0) := by
  unfold regA regularLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * (census 0 o * census 0 o)) = _
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [census]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem regA_ne_top (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regA b lam h n i ≠ ⊤ := by
  induction n generalizing i with
  | zero =>
      rw [regA_zero]
      split_ifs <;> simp
  | succ n ih =>
      rw [regA_rec]
      apply ENNReal.add_ne_top.2
      refine ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_,
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_⟩
      · rw [ENNReal.sum_ne_top]
        intro j _
        exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (ih j)
      · exact ENNReal.mul_ne_top
          (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j))
          (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j))
theorem regM_toReal_rec (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (regM b lam h (n + 1) i).toReal =
      (b : ℝ) * ∑ j : Spin, channel lam i j * (regM b lam h n j).toReal := by
  rw [regM_rec, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  congr 1
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul, toReal_channelPMF]
  · intro j _
    exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j)
theorem regM_formula (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (regM b lam h n i).toReal = (b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin i) := by
  induction n generalizing i with
  | zero =>
      rw [regM_zero]
      split_ifs with hi
      · subst hi
        simp [eSpin]
      · simp [eSpin, hi]
  | succ n ih =>
      rw [regM_toReal_rec]
      calc
        (b : ℝ) * ∑ j : Spin, channel lam i j * (regM b lam h n j).toReal
            = (b : ℝ) * ∑ j : Spin, channel lam i j *
                ((b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin j)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [ih j]
        _ = (b : ℝ) ^ (n + 1) * (1 / 3 + lam ^ (n + 1) * eSpin i) := by
              have h1 : (∑ j : Spin, channel lam i j * (1 / 3 : ℝ)) = 1 / 3 := by
                have := channel_sum lam i
                calc ∑ j : Spin, channel lam i j * (1 / 3 : ℝ)
                    = (∑ j : Spin, channel lam i j) * (1 / 3) := by rw [Finset.sum_mul]
                  _ = 1 / 3 := by rw [this]; ring
              have h2 : (∑ j : Spin, channel lam i j * eSpin j) = lam * eSpin i :=
                channel_mul_eSpin lam i
              have h3 : (∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)) =
                  lam ^ n * (lam * eSpin i) := by
                calc ∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)
                    = ∑ j : Spin, lam ^ n * (channel lam i j * eSpin j) := by
                      apply Finset.sum_congr rfl
                      intro j _; ring
                  _ = lam ^ n * ∑ j : Spin, channel lam i j * eSpin j := by
                      rw [Finset.mul_sum]
                  _ = lam ^ n * (lam * eSpin i) := by rw [h2]
              have hsum : (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
                  (1 / 3 + lam ^ n * (lam * eSpin i)) := by
                rw [show (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
                    ∑ j : Spin, (channel lam i j * (1 / 3 : ℝ) + channel lam i j * (lam ^ n * eSpin j)) by
                  apply Finset.sum_congr rfl
                  intro j _; ring]
                rw [Finset.sum_add_distrib, h1, h3]
              calc
                (b : ℝ) * ∑ j : Spin, channel lam i j *
                    ((b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin j))
                    = (b : ℝ) * ((b : ℝ) ^ n *
                        ∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) := by
                      congr 1
                      calc ∑ j : Spin, channel lam i j *
                            ((b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin j))
                          = ∑ j : Spin, (b : ℝ) ^ n *
                              (channel lam i j * (1 / 3 + lam ^ n * eSpin j)) := by
                            apply Finset.sum_congr rfl
                            intro j _; ring
                        _ = (b : ℝ) ^ n *
                            ∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j) := by
                            rw [Finset.mul_sum]
                _ = (b : ℝ) ^ (n + 1) * (1 / 3 + lam ^ (n + 1) * eSpin i) := by
                      rw [hsum, pow_succ]
                      ring
noncomputable def regC (b : ℕ) (n : ℕ) : ℝ := (b : ℝ) ^ n / 3
noncomputable def regW (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) : ℝ :=
  ∑' o : Observation n,
    (regularLaw b lam h n i o).toReal * ((census n o).toReal - regC b n) ^ 2
theorem regA_toReal_rec (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (regA b lam h (n + 1) i).toReal =
      (b : ℝ) * ∑ j : Spin, channel lam i j * (regA b lam h n j).toReal +
        ((b * (b - 1) : ℕ) : ℝ) *
          ((∑ j : Spin, channel lam i j * (regM b lam h n j).toReal) ^ 2) := by
  rw [regA_rec]
  rw [ENNReal.toReal_add]
  · rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have hA : ((∑ x : Spin, (channelPMF lam h i) x * regA b lam h n x).toReal) =
        ∑ x : Spin, channel lam i x * (regA b lam h n x).toReal := by
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [ENNReal.toReal_mul, toReal_channelPMF]
      · intro j _
        exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regA_ne_top b lam h n j)
    rw [hA, ENNReal.toReal_mul]
    congr 1
    have hM : ((∑ x : Spin, (channelPMF lam h i) x * regM b lam h n x).toReal) =
        ∑ x : Spin, channel lam i x * (regM b lam h n x).toReal := by
      rw [ENNReal.toReal_sum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [ENNReal.toReal_mul, toReal_channelPMF]
      · intro j _
        exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, hM]
    ring
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regA_ne_top b lam h n j))
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top
        (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j))
        (ENNReal.sum_ne_top.2 fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (regM_ne_top b lam h n j)))
theorem regW_eq (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regW b lam h n i = (regA b lam h n i).toReal -
      2 * regC b n * (regM b lam h n i).toReal + (regC b n) ^ 2 := by
  unfold regW regA regM
  have hA : (∑' o : Observation n, (regularLaw b lam h n i o).toReal * (census n o).toReal ^ 2) =
      (∑' o : Observation n, regularLaw b lam h n i o * (census n o * census n o)).toReal := by
    rw [show (∑' o : Observation n, ((regularLaw b lam h n i) o).toReal * (census n o).toReal ^ 2)
        = ∑' o : Observation n, ((regularLaw b lam h n i) o).toReal *
            ((census n o * census n o).toReal) by
      apply tsum_congr
      intro o
      rw [pow_two, ENNReal.toReal_mul]]
    rw [TheoremOS.Probability.tsum_toReal_mul_toReal (regularLaw b lam h n i)
      (fun o => census n o * census n o) (by simpa [regA] using regA_ne_top b lam h n i)]
  have hM : (∑' o : Observation n, (regularLaw b lam h n i o).toReal * (census n o).toReal) =
      (∑' o : Observation n, regularLaw b lam h n i o * census n o).toReal := by
    rw [TheoremOS.Probability.tsum_toReal_mul_toReal (regularLaw b lam h n i)
      (fun o => census n o) (by simpa [regM] using regM_ne_top b lam h n i)]
  rw [TheoremOS.Probability.tsum_mul_sub_sq]
  · rw [hA, hM]
  · exact by
      simpa [pow_two] using
        (TheoremOS.Probability.summable_toReal_mul_toReal (regularLaw b lam h n i)
          (fun o => census n o * census n o)
          (by simpa [regA] using regA_ne_top b lam h n i))
theorem regM_center (b : ℕ) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (∑ j : Spin, channel lam i j * (regM b lam h n j).toReal) - regC b n =
      (b : ℝ) ^ n * lam ^ (n + 1) * eSpin i := by
  have hsum : (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
      1 / 3 + lam ^ (n + 1) * eSpin i := by
    have h1 : (∑ j : Spin, channel lam i j * (1 / 3 : ℝ)) = 1 / 3 := by
      have := channel_sum lam i
      calc ∑ j : Spin, channel lam i j * (1 / 3 : ℝ)
          = (∑ j : Spin, channel lam i j) * (1 / 3) := by rw [Finset.sum_mul]
        _ = 1 / 3 := by rw [this]; ring
    have h3 : (∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)) =
        lam ^ n * (lam * eSpin i) := by
      calc ∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)
          = ∑ j : Spin, lam ^ n * (channel lam i j * eSpin j) := by
            apply Finset.sum_congr rfl
            intro j _; ring
        _ = lam ^ n * ∑ j : Spin, channel lam i j * eSpin j := by
            rw [Finset.mul_sum]
        _ = lam ^ n * (lam * eSpin i) := by rw [channel_mul_eSpin]
    rw [show (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
        ∑ j : Spin, (channel lam i j * (1 / 3 : ℝ) + channel lam i j * (lam ^ n * eSpin j)) by
      apply Finset.sum_congr rfl
      intro j _; ring]
    rw [Finset.sum_add_distrib, h1, h3]
    rw [pow_succ]
    ring
  have hfactor : (∑ j : Spin, channel lam i j *
        ((b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin j))) =
      (b : ℝ) ^ n * ∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  calc
    (∑ j : Spin, channel lam i j * (regM b lam h n j).toReal) - regC b n
        = (∑ j : Spin, channel lam i j *
            ((b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin j))) - (b : ℝ) ^ n / 3 := by
          rw [regC]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [regM_formula]
    _ = (b : ℝ) ^ n * (1 / 3 + lam ^ (n + 1) * eSpin i) - (b : ℝ) ^ n / 3 := by
          rw [hfactor, hsum]
    _ = (b : ℝ) ^ n * lam ^ (n + 1) * eSpin i := by ring
theorem regW_rec (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    regW b lam h (n + 1) i =
      (b : ℝ) * (∑ j : Spin, channel lam i j * regW b lam h n j) +
        ((b * (b - 1) : ℕ) : ℝ) *
          (((b : ℝ) ^ n * lam ^ (n + 1) * eSpin i) ^ 2) := by
  have hB : ((b * (b - 1) : ℕ) : ℝ) = (b : ℝ) * ((b : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ b)]
    norm_num
  have hsumW : (∑ j : Spin, channel lam i j * regW b lam h n j) =
      (∑ j : Spin, channel lam i j * (regA b lam h n j).toReal) -
        2 * regC b n * (∑ j : Spin, channel lam i j * (regM b lam h n j).toReal) +
        (regC b n) ^ 2 := by
    calc
      (∑ j : Spin, channel lam i j * regW b lam h n j)
          = ∑ j : Spin, channel lam i j *
              ((regA b lam h n j).toReal - 2 * regC b n * (regM b lam h n j).toReal +
                (regC b n) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [regW_eq]
      _ = (∑ j : Spin, channel lam i j * (regA b lam h n j).toReal) -
            2 * regC b n * (∑ j : Spin, channel lam i j * (regM b lam h n j).toReal) +
            (regC b n) ^ 2 := by
            rw [show (∑ j : Spin, channel lam i j *
                ((regA b lam h n j).toReal - 2 * regC b n * (regM b lam h n j).toReal +
                  (regC b n) ^ 2)) =
                ∑ j : Spin, (channel lam i j * (regA b lam h n j).toReal -
                  2 * regC b n * (channel lam i j * (regM b lam h n j).toReal) +
                  channel lam i j * (regC b n) ^ 2) by
              apply Finset.sum_congr rfl
              intro j _; ring]
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [show (∑ x, 2 * regC b n * (channel lam i x * (regM b lam h n x).toReal)) =
                2 * regC b n * ∑ x, channel lam i x * (regM b lam h n x).toReal by
              rw [Finset.mul_sum]] 
            rw [show (∑ x, channel lam i x * regC b n ^ 2) = regC b n ^ 2 by
              rw [← Finset.sum_mul, channel_sum]
              ring]
  rw [regW_eq b lam h (n + 1) i, regA_toReal_rec, regM_toReal_rec, hsumW]
  have hc : regC b (n + 1) = (b : ℝ) * regC b n := by
    rw [regC, regC, pow_succ]; ring
  rw [hc]
  set X := ∑ j : Spin, channel lam i j * (regM b lam h n j).toReal
  have hcenter := regM_center b lam h n i
  rw [← hcenter]
  rw [hB]
  ring
theorem regW_zero (b : ℕ) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    regW b lam h 0 i = eSpin i ^ 2 := by
  unfold regW regularLaw observedLaw regC
  simp only [pow_zero, Nat.cast_one]
  change (∑' o : Spin, ((PMF.pure i : PMF Spin) o).toReal *
    ((census 0 o).toReal - (1 : ℝ) / 3) ^ 2) = eSpin i ^ 2
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    by_cases hi : i = (1 : Spin)
    · simp [census, eSpin, hi]
    · simp [census, eSpin, hi]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem regW_bound (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b : ℝ) * lam ^ 2) (n : ℕ) (i : Spin) :
    regW b lam h n i ≤
      (4 * ((b : ℝ) * lam ^ 2) / (9 * ((b : ℝ) * lam ^ 2 - 1))) *
        ((((b : ℝ) * lam) ^ 2) ^ n) := by
  set r : ℝ := (b : ℝ) * lam ^ 2 with hr
  set s : ℝ := ((b : ℝ) * lam) ^ 2 with hs
  set Q : ℝ := 4 * r / (9 * (r - 1)) with hQ
  have hr1 : 1 < r := hcrit
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrm1 : 0 < r - 1 := by linarith
  have hs0 : 0 ≤ s := sq_nonneg _
  have hs_eq : s = (b : ℝ) * r := by rw [hs, hr]; ring
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hQbase : (4 : ℝ) / 9 ≤ Q := by
    rw [hQ]
    have hfrac : (1 : ℝ) ≤ r / (r - 1) := by
      rw [le_div_iff₀ hrm1]
      linarith
    calc (4 : ℝ) / 9 = (4 / 9) * 1 := by ring
      _ ≤ (4 / 9) * (r / (r - 1)) := by gcongr
      _ = 4 * r / (9 * (r - 1)) := by field_simp
  have hB : ((b * (b - 1) : ℕ) : ℝ) = (b : ℝ) * ((b : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ b)]
    norm_num
  induction n generalizing i with
  | zero =>
      rw [regW_zero, pow_zero, mul_one]
      exact (eSpin_sq_le i).trans hQbase
  | succ n ih =>
      rw [regW_rec b hb lam h n i]
      have hSum : (∑ j : Spin, channel lam i j * regW b lam h n j) ≤ Q * s ^ n := by
        calc
          (∑ j : Spin, channel lam i j * regW b lam h n j)
              ≤ ∑ j : Spin, channel lam i j * (Q * s ^ n) := by
                apply Finset.sum_le_sum
                intro j _
                exact mul_le_mul_of_nonneg_left (ih j) (channel_nonneg h i j)
          _ = Q * s ^ n := by
                rw [← Finset.sum_mul, channel_sum]
                ring
      have hterm : (((b : ℝ) ^ n * lam ^ (n + 1) * eSpin i) ^ 2) ≤
          s ^ n * lam ^ 2 * ((4 : ℝ) / 9) := by
        have hbase : ((b : ℝ) ^ n * lam ^ (n + 1)) ^ 2 = s ^ n * lam ^ 2 := by
          have hbl : (b : ℝ) ^ n * lam ^ (n + 1) = ((b : ℝ) * lam) ^ n * lam := by
            rw [mul_pow, pow_succ]
            ring
          rw [hbl, mul_pow, hs, pow_right_comm]
        calc
          (((b : ℝ) ^ n * lam ^ (n + 1) * eSpin i) ^ 2)
              = ((b : ℝ) ^ n * lam ^ (n + 1)) ^ 2 * eSpin i ^ 2 := by ring
          _ = (s ^ n * lam ^ 2) * eSpin i ^ 2 := by rw [hbase]
          _ ≤ (s ^ n * lam ^ 2) * ((4 : ℝ) / 9) := by
                gcongr
                exact eSpin_sq_le i
          _ = s ^ n * lam ^ 2 * ((4 : ℝ) / 9) := by ring
      calc
        (b : ℝ) * (∑ j : Spin, channel lam i j * regW b lam h n j) +
            ((b * (b - 1) : ℕ) : ℝ) *
              (((b : ℝ) ^ n * lam ^ (n + 1) * eSpin i) ^ 2)
            ≤ (b : ℝ) * (Q * s ^ n) +
                ((b * (b - 1) : ℕ) : ℝ) * (s ^ n * lam ^ 2 * ((4 : ℝ) / 9)) := by
              gcongr
        _ = ((b : ℝ) * Q + ((b * (b - 1) : ℕ) : ℝ) * lam ^ 2 * ((4 : ℝ) / 9)) * s ^ n := by
              ring
        _ ≤ Q * s ^ (n + 1) := by
              rw [pow_succ]
              have hcoef : (b : ℝ) * Q +
                  ((b * (b - 1) : ℕ) : ℝ) * lam ^ 2 * (4 / 9) ≤ Q * s := by
                rw [hB]
                rw [hs_eq, hQ]
                have hb1 : (0 : ℝ) ≤ (b : ℝ) - 1 := by
                  have : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
                  linarith
                have hlam : ((b : ℝ) - 1) * lam ^ 2 ≤ r := by
                  rw [hr]
                  nlinarith [sq_nonneg lam]
                have hcoef0 : (b : ℝ) * (4 * r / (9 * (r - 1))) +
                    (b : ℝ) * ((b : ℝ) - 1) * lam ^ 2 * (4 / 9) ≤
                    (4 * r / (9 * (r - 1))) * ((b : ℝ) * r) := by
                  field_simp [hrm1.ne']
                  nlinarith [hlam, hr0, hrm1]
                simpa [mul_assoc, mul_left_comm, mul_comm] using hcoef0
              calc
                ((b : ℝ) * Q + ((b * (b - 1) : ℕ) : ℝ) * lam ^ 2 * ((4 : ℝ) / 9)) * s ^ n
                    ≤ (Q * s) * s ^ n := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hs0 n)
                _ = Q * s ^ (n + 1) := by ring

theorem poisson_mean (d : ℝ) (hd : 0 ≤ d) :
    (∑' k : ℕ, poissonOffspring d hd k * ((k : ℕ) : ENNReal)) = ENNReal.ofReal d := by
  have h := TheoremOS.Probability.tsum_ofReal_poissonWeight_mul (d := d) hd
  have hfun : (fun k : ℕ => poissonOffspring d hd k * ((k : ℕ) : ENNReal)) =
      fun k : ℕ => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)) * ((k : ℕ) : ENNReal) := by
    funext k; rfl
  rw [hfun]; exact h

noncomputable def poisM (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, poissonLaw d hd lam h n i o * census n o

theorem poisM_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisM d hd lam h 0 i = (if i = (1 : Spin) then (1 : ENNReal) else 0) := by
  unfold poisM poissonLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * census 0 o) = _
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [census]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp

theorem poisM_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisM d hd lam h (n + 1) i =
      ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j := by
  unfold poisM
  have hb := (isBroadcastLaw_observedLaw (poissonOffspring d hd) lam h).tsum_mul_census
    (O := Observation) (K := channelPMF lam h) (N := poissonOffspring d hd)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (poissonOffspring d hd) lam h) census (fun n s => census_succ n s) n i
  rw [poisson_mean d hd] at hb
  simpa [poissonLaw] using hb

theorem poisM_bound (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisM d hd lam h n i ≤ (ENNReal.ofReal d) ^ n := by
  induction n generalizing i with
  | zero =>
      rw [poisM_zero]
      split_ifs <;> simp
  | succ n ih =>
      rw [poisM_rec]
      calc
        ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j
            ≤ ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * (ENNReal.ofReal d) ^ n := by
              gcongr with j
              exact ih j
        _ = ENNReal.ofReal d * ((ENNReal.ofReal d) ^ n * ∑ j : Spin, channelPMF lam h i j) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (ENNReal.ofReal d) ^ (n + 1) := by
              rw [channelPMF_tsum, mul_one, pow_succ]
              ring

theorem poisM_ne_top (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisM d hd lam h n i ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (poisM_bound d hd lam h n i)

theorem poisM_toReal_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (poisM d hd lam h (n + 1) i).toReal =
      d * ∑ j : Spin, channel lam i j * (poisM d hd lam h n j).toReal := by
  rw [poisM_rec, ENNReal.toReal_mul, ENNReal.toReal_ofReal hd]
  congr 1
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul, toReal_channelPMF]
  · intro j _
    exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisM_ne_top d hd lam h n j)

theorem poisM_formula (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (poisM d hd lam h n i).toReal = d ^ n * (1 / 3 + lam ^ n * eSpin i) := by
  induction n generalizing i with
  | zero =>
      rw [poisM_zero]
      split_ifs with hi
      · subst hi
        simp [eSpin]
      · simp [eSpin, hi]
  | succ n ih =>
      rw [poisM_toReal_rec]
      have h1 : (∑ j : Spin, channel lam i j * (1 / 3 : ℝ)) = 1 / 3 := by
        calc ∑ j : Spin, channel lam i j * (1 / 3 : ℝ)
            = (∑ j : Spin, channel lam i j) * (1 / 3) := by rw [Finset.sum_mul]
          _ = 1 / 3 := by rw [channel_sum]; ring
      have h3 : (∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)) =
          lam ^ n * (lam * eSpin i) := by
        calc ∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)
            = ∑ j : Spin, lam ^ n * (channel lam i j * eSpin j) := by
              apply Finset.sum_congr rfl
              intro j _; ring
          _ = lam ^ n * ∑ j : Spin, channel lam i j * eSpin j := by rw [Finset.mul_sum]
          _ = lam ^ n * (lam * eSpin i) := by rw [channel_mul_eSpin]
      have hsum : (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
          1 / 3 + lam ^ (n + 1) * eSpin i := by
        rw [show (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
            ∑ j : Spin, (channel lam i j * (1 / 3 : ℝ) + channel lam i j * (lam ^ n * eSpin j)) by
          apply Finset.sum_congr rfl
          intro j _; ring]
        rw [Finset.sum_add_distrib, h1, h3, pow_succ]
        ring
      have hfactor : (∑ j : Spin, channel lam i j *
            (d ^ n * (1 / 3 + lam ^ n * eSpin j))) =
          d ^ n * ∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
      calc
        d * ∑ j : Spin, channel lam i j * (poisM d hd lam h n j).toReal
            = d * ∑ j : Spin, channel lam i j *
                (d ^ n * (1 / 3 + lam ^ n * eSpin j)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [ih j]
        _ = d * (d ^ n * (1 / 3 + lam ^ (n + 1) * eSpin i)) := by
              rw [hfactor, hsum]
        _ = d ^ (n + 1) * (1 / 3 + lam ^ (n + 1) * eSpin i) := by
              rw [pow_succ]; ring
noncomputable def totalCensus : (n : ℕ) → Observation n → ENNReal
  | 0 => fun _ => 1
  | n + 1 => fun s => (s.map (totalCensus n)).sum

theorem totalCensus_succ (n : ℕ) (s : Multiset (Observation n)) :
    totalCensus (n + 1) s = (s.map (totalCensus n)).sum := rfl

noncomputable def poisT (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, poissonLaw d hd lam h n i o * totalCensus n o

theorem poisT_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisT d hd lam h 0 i = 1 := by
  unfold poisT poissonLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * totalCensus 0 o) = 1
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [totalCensus]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp

theorem poisT_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisT d hd lam h (n + 1) i =
      ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j := by
  unfold poisT
  have hb := (isBroadcastLaw_observedLaw (poissonOffspring d hd) lam h).tsum_mul_census
    (O := Observation) (K := channelPMF lam h) (N := poissonOffspring d hd)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (poissonOffspring d hd) lam h) totalCensus
    (fun n s => totalCensus_succ n s) n i
  rw [poisson_mean d hd] at hb
  simpa [poissonLaw] using hb

theorem poisT_eq (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisT d hd lam h n i = (ENNReal.ofReal d) ^ n := by
  induction n generalizing i with
  | zero => rw [poisT_zero, pow_zero]
  | succ n ih =>
      rw [poisT_rec]
      calc
        ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j
            = ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * (ENNReal.ofReal d) ^ n := by
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [ih j]
        _ = ENNReal.ofReal d * ((ENNReal.ofReal d) ^ n * ∑ j : Spin, channelPMF lam h i j) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = (ENNReal.ofReal d) ^ (n + 1) := by
              rw [channelPMF_tsum, mul_one, pow_succ]
              ring

theorem poisT_ne_top (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisT d hd lam h n i ≠ ⊤ := by
  rw [poisT_eq]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

theorem poisT_formula (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (poisT d hd lam h n i).toReal = d ^ n := by
  rw [poisT_eq, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd]

theorem multiset_sum_ne_top {α : Type*} (s : Multiset α) (f : α → ENNReal)
    (hf : ∀ a ∈ s, f a ≠ ⊤) : (s.map f).sum ≠ ⊤ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact ENNReal.add_ne_top.2
        ⟨hf x (by simp), ih fun a ha => hf a (by simp [ha])⟩

theorem toReal_multiset_sum {α : Type*} (s : Multiset α) (f : α → ENNReal)
    (hf : ∀ a ∈ s, f a ≠ ⊤) :
    ((s.map f).sum).toReal = (s.map (fun a => (f a).toReal)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
      have hx : f x ≠ ⊤ := hf x (by simp)
      have ht : ∀ a ∈ t, f a ≠ ⊤ := fun a ha => hf a (by simp [ha])
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ENNReal.toReal_add hx (multiset_sum_ne_top t f ht), ih ht]

theorem census_ne_top (n : ℕ) (o : Observation n) : census n o ≠ ⊤ := by
  induction n with
  | zero =>
      change (if (show Spin from o) = (1 : Spin) then (1 : ENNReal) else 0) ≠ ⊤
      split_ifs <;> simp
  | succ n ih =>
      change (o.map (census n)).sum ≠ ⊤
      exact multiset_sum_ne_top o (census n) fun a _ => ih a

theorem totalCensus_ne_top (n : ℕ) (o : Observation n) : totalCensus n o ≠ ⊤ := by
  induction n with
  | zero => simp [totalCensus]
  | succ n ih =>
      change (o.map (totalCensus n)).sum ≠ ⊤
      exact multiset_sum_ne_top o (totalCensus n) fun a _ => ih a
theorem multiset_sum_map_sub {α : Type*} (s : Multiset α) (f g : α → ℝ) :
    (s.map (fun a => f a - g a)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]; ring

theorem leafSum_eSpin_eq (n : ℕ) (o : Observation n) :
    leafSum eSpin n o = (census n o).toReal - (1 / 3) * (totalCensus n o).toReal := by
  induction n with
  | zero =>
      change eSpin o = (if (show Spin from o) = (1 : Spin) then (1:ENNReal) else 0).toReal
        - (1/3) * (1:ENNReal).toReal
      simp [eSpin]
      split_ifs <;> norm_num
  | succ n ih =>
      set o' : Multiset (Observation n) := o
      change (o'.map (leafSum eSpin n)).sum =
        ((o'.map (census n)).sum).toReal - (1/3) * ((o'.map (totalCensus n)).sum).toReal
      rw [toReal_multiset_sum o' (census n) (fun a _ => census_ne_top n a),
        toReal_multiset_sum o' (totalCensus n) (fun a _ => totalCensus_ne_top n a)]
      have hcongr : (o'.map (leafSum eSpin n)) =
          (o'.map fun a => (census n a).toReal - (1/3) * (totalCensus n a).toReal) := by
        apply Multiset.map_congr rfl
        intro a _
        exact ih a
      rw [hcongr, ← Multiset.sum_map_mul_left (s := o') (a := (1/3 : ℝ))
        (f := fun a => (totalCensus n a).toReal)]
      exact multiset_sum_map_sub (α := Observation n) o'
        (fun a => (census n a).toReal) (fun a => (1/3) * (totalCensus n a).toReal)

theorem poissonLeaf_mean (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (∑' o : Observation n, (poissonLaw d hd lam h n i o).toReal * leafSum eSpin n o)
      = ((d : ℝ) * lam) ^ n * eSpin i := by
  have hsm : Summable fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * (census n o).toReal :=
    TheoremOS.Probability.summable_toReal_mul_toReal _ _ (poisM_ne_top d hd lam h n i)
  have hst : Summable fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * ((1 / 3) * (totalCensus n o).toReal) := by
    have h0 := TheoremOS.Probability.summable_toReal_mul_toReal
      (poissonLaw d hd lam h n i) (totalCensus n) (poisT_ne_top d hd lam h n i)
    refine (h0.mul_right (1 / 3)).congr fun o => ?_
    ring
  have hsplit : (∑' o : Observation n,
        (poissonLaw d hd lam h n i o).toReal * leafSum eSpin n o)
      = (∑' o : Observation n, (poissonLaw d hd lam h n i o).toReal * (census n o).toReal)
        - (∑' o : Observation n,
            (poissonLaw d hd lam h n i o).toReal * ((1 / 3) * (totalCensus n o).toReal)) := by
    rw [← Summable.tsum_sub hsm hst]
    apply tsum_congr
    intro o
    rw [leafSum_eSpin_eq]
    ring
  have hM : (∑' o : Observation n, (poissonLaw d hd lam h n i o).toReal * (census n o).toReal)
      = (poisM d hd lam h n i).toReal :=
    TheoremOS.Probability.tsum_toReal_mul_toReal _ _ (poisM_ne_top d hd lam h n i)
  have hT : (∑' o : Observation n,
        (poissonLaw d hd lam h n i o).toReal * ((1 / 3) * (totalCensus n o).toReal))
      = (1 / 3) * (poisT d hd lam h n i).toReal := by
    rw [show (∑' o : Observation n,
          (poissonLaw d hd lam h n i o).toReal * ((1 / 3) * (totalCensus n o).toReal))
        = ∑' o : Observation n,
            (1 / 3) * ((poissonLaw d hd lam h n i o).toReal * (totalCensus n o).toReal) from
      tsum_congr fun o => by ring]
    rw [tsum_mul_left]
    rw [TheoremOS.Probability.tsum_toReal_mul_toReal (poissonLaw d hd lam h n i) (totalCensus n)
      (poisT_ne_top d hd lam h n i)]
    rfl
  rw [hsplit, hM, hT, poisM_formula, poisT_formula, mul_pow]
  ring

theorem poissonLeaf_first_moment (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) (n : ℕ) (i : Spin) :
    (∑' o : Observation n, (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal
        * leafSum eSpin n o) = ((d : ℝ) * lam) ^ n * eSpin i :=
  poissonLeaf_mean d (le_trans (by norm_num) hd.le) lam h n i
theorem poisson_reconstructs_of_leaf_moments (d : ℝ) (hd : 1 < d) (lam : ℝ)
    (h : Admissible lam) (hcrit : 1 < d * lam ^ 2)
    (hfirst : ∀ (n : ℕ) (i : Spin),
      (∑' o : Observation n,
        (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal * leafSum eSpin n o)
        = ((d : ℝ) * lam) ^ n * eSpin i)
    (hsecond : (∀ (n : ℕ) (i : Spin), Summable (fun o : Observation n =>
        (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
          (leafSum eSpin n o) ^ 2)) ∧
      (∀ (n : ℕ) (i : Spin),
        (∑' o : Observation n,
          (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
            (leafSum eSpin n o) ^ 2)
          ≤ ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d : ℝ) * lam) ^ (2 * n))) :
    Reconstructs (poissonAdvantage d hd lam h) := by
  classical
  have hd0 : 0 ≤ d := le_trans (by norm_num) hd.le
  set s : ℝ := (d * lam) ^ 2 with hs
  set q : ℝ := 1 / (d * lam ^ 2) with hq
  set C : ℝ := (4 / 9) / (1 - q) with hC
  have hdl2 : 0 < d * lam ^ 2 := lt_trans zero_lt_one hcrit
  have hqpos : 0 < q := by rw [hq]; exact div_pos one_pos hdl2
  have hq1 : q < 1 := by
    rw [hq, div_lt_one hdl2]
    linarith
  have h1q : 0 < 1 - q := by linarith
  have hCpos : 0 < C := by rw [hC]; exact div_pos (by norm_num) h1q
  have hdlne : d * lam ≠ 0 := by
    intro h0
    nlinarith [hcrit]
  have hs_pos : 0 < s := by
    rw [hs, pow_two]
    exact mul_self_pos.mpr hdlne
  have hs_pow : ∀ n : ℕ, s ^ n = (d * lam) ^ (2 * n) := by
    intro n
    rw [hs, ← pow_mul]
  have hconst : ∀ n : ℕ, ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d : ℝ) * lam) ^ (2 * n)
      = C * s ^ n := by
    intro n
    rw [hs_pow n]
  have hTV : ∀ n : ℕ, (1 : ℝ) / (4 * C) ≤
      TheoremOS.Probability.pmfTV (poissonLaw d hd0 lam h n (1 : Spin))
        (poissonLaw d hd0 lam h n (0 : Spin)) := by
    intro n
    set p : PMF (Observation n) := poissonLaw d hd0 lam h n (1 : Spin) with hp_def
    set q0 : PMF (Observation n) := poissonLaw d hd0 lam h n (0 : Spin) with hq0_def
    set S : Observation n → ℝ := fun o => leafSum eSpin n o with hS_def
    have hp_sum : Summable fun a => (p a).toReal * S a ^ 2 := by
      simpa [p, S] using hsecond.1 n (1 : Spin)
    have hq_sum : Summable fun a => (q0 a).toReal * S a ^ 2 := by
      simpa [q0, S] using hsecond.1 n (0 : Spin)
    have hM1 : (∑' o : Observation n, (p o).toReal * S o) =
        (d * lam) ^ n * eSpin (1 : Spin) := by
      simpa [p, S] using hfirst n (1 : Spin)
    have hM0 : (∑' o : Observation n, (q0 o).toReal * S o) =
        (d * lam) ^ n * eSpin (0 : Spin) := by
      simpa [q0, S] using hfirst n (0 : Spin)
    have hmean : (∑' o : Observation n, (p o).toReal * S o) -
        (∑' o : Observation n, (q0 o).toReal * S o) = (d * lam) ^ n := by
      rw [hM1, hM0, ← mul_sub, eSpin_one_sub_zero, mul_one]
    have hsquare : ((∑' o : Observation n, (p o).toReal * S o) -
        (∑' o : Observation n, (q0 o).toReal * S o)) ^ 2 = s ^ n := by
      rw [hmean, hs]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    have hboundp : (∑' o : Observation n, (p o).toReal * S o ^ 2) ≤ C * s ^ n := by
      have h2 := hsecond.2 n (1 : Spin)
      rw [hconst n] at h2
      simpa [p, S] using h2
    have hboundq : (∑' o : Observation n, (q0 o).toReal * S o ^ 2) ≤ C * s ^ n := by
      have h2 := hsecond.2 n (0 : Spin)
      rw [hconst n] at h2
      simpa [q0, S] using h2
    have hmain := TheoremOS.Probability.sq_sub_le_pmfTV_mul_centred p q0 S 0 hp_sum hq_sum
    have hmain' : ((∑' o : Observation n, (p o).toReal * S o) -
        (∑' o : Observation n, (q0 o).toReal * S o)) ^ 2 ≤
        2 * TheoremOS.Probability.pmfTV p q0 *
          ((∑' o : Observation n, (p o).toReal * S o ^ 2) +
           (∑' o : Observation n, (q0 o).toReal * S o ^ 2)) := by
      simpa only [sub_zero] using hmain
    have hWsum : (∑' o : Observation n, (p o).toReal * S o ^ 2) +
        (∑' o : Observation n, (q0 o).toReal * S o ^ 2) ≤ 2 * (C * s ^ n) := by
      linarith
    have hle : s ^ n ≤ 2 * TheoremOS.Probability.pmfTV p q0 * (2 * (C * s ^ n)) := by
      calc
        s ^ n = ((∑' o : Observation n, (p o).toReal * S o) -
            (∑' o : Observation n, (q0 o).toReal * S o)) ^ 2 := hsquare.symm
        _ ≤ 2 * TheoremOS.Probability.pmfTV p q0 *
              ((∑' o : Observation n, (p o).toReal * S o ^ 2) +
               (∑' o : Observation n, (q0 o).toReal * S o ^ 2)) := hmain'
        _ ≤ 2 * TheoremOS.Probability.pmfTV p q0 * (2 * (C * s ^ n)) := by
              apply mul_le_mul_of_nonneg_left hWsum
              have htv0 : 0 ≤ TheoremOS.Probability.pmfTV p q0 :=
                TheoremOS.Probability.pmfTV_nonneg p q0
              positivity
    have hspos : 0 < s ^ n := pow_pos hs_pos n
    have hquad : 1 ≤ 4 * C * TheoremOS.Probability.pmfTV p q0 := by
      have hle' : s ^ n ≤ (4 * C * s ^ n) * TheoremOS.Probability.pmfTV p q0 := by
        calc
          s ^ n ≤ 2 * TheoremOS.Probability.pmfTV p q0 * (2 * (C * s ^ n)) := hle
          _ = (4 * C * s ^ n) * TheoremOS.Probability.pmfTV p q0 := by ring
      have hle2 : s ^ n * 1 ≤ s ^ n * (4 * C * TheoremOS.Probability.pmfTV p q0) := by
        calc
          s ^ n * 1 = s ^ n := by ring
          _ ≤ (4 * C * s ^ n) * TheoremOS.Probability.pmfTV p q0 := hle'
          _ = s ^ n * (4 * C * TheoremOS.Probability.pmfTV p q0) := by ring
      exact (mul_le_mul_iff_of_pos_left hspos).mp hle2
    have htv : (1 : ℝ) / (4 * C) ≤ TheoremOS.Probability.pmfTV p q0 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * C)]
      simpa [mul_comm] using hquad
    simpa [p, q0] using htv
  have hAdv : ∀ n : ℕ, (1 : ℝ) / (12 * C) ≤
      TheoremOS.Probability.reconAdvantage (poissonLaw d hd0 lam h n) := by
    intro n
    have htv := hTV n
    have hcard := TheoremOS.Probability.pmfTV_le_card_mul_reconAdvantage
      (poissonLaw d hd0 lam h n) (1 : Spin) (0 : Spin)
    have hcard3 : (Fintype.card Spin : ℝ) = 3 := by simp
    rw [hcard3] at hcard
    have h1 : (1 : ℝ) / (4 * C) ≤ 3 * TheoremOS.Probability.reconAdvantage
        (poissonLaw d hd0 lam h n) := htv.trans hcard
    have heq : (1 : ℝ) / (4 * C) = 3 * (1 / (12 * C)) := by
      field_simp
      ring
    rw [heq] at h1
    exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 3)).mp h1
  have hbc := isBroadcastLaw_observedLaw (poissonOffspring d hd0) lam h
  have hiff := hbc.exists_pos_tendsto_iff
    (leaf := fun i : Spin => i) (up := fun _ s => s) (law := observedLaw (poissonOffspring d hd0) lam h)
    (fun _ _ hij => hij) (fun _ _ _ hij => hij)
  have hpos : ∃ ε, 0 < ε ∧ ∀ n : ℕ,
      ε ≤ TheoremOS.Probability.reconAdvantage (observedLaw (poissonOffspring d hd0) lam h n) := by
    refine ⟨1 / (12 * C), by positivity, ?_⟩
    intro n
    simpa [poissonLaw] using hAdv n
  rcases hiff.mpr hpos with ⟨L, hL, hlim⟩
  refine ⟨L, hL, ?_⟩
  have hfun : poissonAdvantage d hd lam h = fun n =>
      TheoremOS.Probability.reconAdvantage (observedLaw (poissonOffspring d hd0) lam h n) := by
    funext n
    simp only [poissonAdvantage, poissonLaw]
    exact advantage_eq_reconAdvantage _
  rw [hfun]
  exact hlim

theorem poisson_descFactorial (d : ℝ) (hd : 0 ≤ d) :
    (∑' k : ℕ, poissonOffspring d hd k * (((k * (k - 1) : ℕ) : ℕ) : ENNReal)) =
      ENNReal.ofReal (d ^ 2) := by
  have h := TheoremOS.Probability.tsum_ofReal_poissonWeight_mul_descFactorial (d := d) hd
  have hfun : (fun k : ℕ => poissonOffspring d hd k * ((k * (k - 1) : ℕ) : ENNReal)) =
      fun k : ℕ => ENNReal.ofReal (Real.exp (-d) * d ^ k / (k.factorial : ℝ)) *
        ((k * (k - 1) : ℕ) : ENNReal) := by
    funext k; rfl
  rw [hfun]; exact h
theorem census_le_totalCensus : ∀ (n : ℕ) (o : Observation n), census n o ≤ totalCensus n o := by
  intro n
  induction n with
  | zero =>
      intro o
      change (if (show Spin from o) = (1 : Spin) then (1 : ENNReal) else 0) ≤ 1
      split_ifs <;> simp
  | succ n ih =>
      intro s
      change (s.map (census n)).sum ≤ (s.map (totalCensus n)).sum
      induction s using Multiset.induction_on with
      | empty => simp
      | cons x t iht =>
          simp only [Multiset.map_cons, Multiset.sum_cons]
          exact add_le_add (ih x) iht
noncomputable def poisA (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, poissonLaw d hd lam h n i o * (census n o * census n o)
noncomputable def poisB (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, poissonLaw d hd lam h n i o * (census n o * totalCensus n o)
noncomputable def poisC (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑' o : Observation n, poissonLaw d hd lam h n i o * (totalCensus n o * totalCensus n o)
theorem poisA_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisA d hd lam h (n + 1) i =
      ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisA d hd lam h n j +
      ENNReal.ofReal (d ^ 2) *
        ((∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j) *
         (∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j)) := by
  unfold poisA
  have hb := (isBroadcastLaw_observedLaw (poissonOffspring d hd) lam h).tsum_mul_census_mul_census
    (O := Observation) (K := channelPMF lam h) (N := poissonOffspring d hd)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (poissonOffspring d hd) lam h) census census
    (fun n s => census_succ n s) (fun n s => census_succ n s) n i
  rw [poisson_mean d hd, poisson_descFactorial d hd] at hb
  simpa [poissonLaw, poisM] using hb
theorem poisB_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisB d hd lam h (n + 1) i =
      ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisB d hd lam h n j +
      ENNReal.ofReal (d ^ 2) *
        ((∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j) *
         (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j)) := by
  unfold poisB
  have hb := (isBroadcastLaw_observedLaw (poissonOffspring d hd) lam h).tsum_mul_census_mul_census
    (O := Observation) (K := channelPMF lam h) (N := poissonOffspring d hd)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (poissonOffspring d hd) lam h) census totalCensus
    (fun n s => census_succ n s) (fun n s => totalCensus_succ n s) n i
  rw [poisson_mean d hd, poisson_descFactorial d hd] at hb
  simpa [poissonLaw, poisM, poisT] using hb
theorem poisC_rec (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisC d hd lam h (n + 1) i =
      ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisC d hd lam h n j +
      ENNReal.ofReal (d ^ 2) *
        ((∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j) *
         (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j)) := by
  unfold poisC
  have hb := (isBroadcastLaw_observedLaw (poissonOffspring d hd) lam h).tsum_mul_census_mul_census
    (O := Observation) (K := channelPMF lam h) (N := poissonOffspring d hd)
    (leaf := fun i : Spin => i) (up := fun _ s => s)
    (law := observedLaw (poissonOffspring d hd) lam h) totalCensus totalCensus
    (fun n s => totalCensus_succ n s) (fun n s => totalCensus_succ n s) n i
  rw [poisson_mean d hd, poisson_descFactorial d hd] at hb
  simpa [poissonLaw, poisT] using hb
theorem poisA_le_poisC (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisA d hd lam h n i ≤ poisC d hd lam h n i := by
  unfold poisA poisC
  apply ENNReal.tsum_le_tsum
  intro o
  exact mul_le_mul' (le_refl _)
    (mul_le_mul' (census_le_totalCensus n o) (census_le_totalCensus n o))
theorem poisB_le_poisC (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisB d hd lam h n i ≤ poisC d hd lam h n i := by
  unfold poisB poisC
  apply ENNReal.tsum_le_tsum
  intro o
  exact mul_le_mul' (le_refl _)
    (mul_le_mul' (census_le_totalCensus n o) (le_refl _))
theorem channelPMF_sum_mul_const (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j) = (ENNReal.ofReal d) ^ n := by
  calc (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j)
      = ∑ j : Spin, channelPMF lam h i j * (ENNReal.ofReal d) ^ n := by
        apply Finset.sum_congr rfl
        intro j _; rw [poisT_eq]
    _ = (∑ j : Spin, channelPMF lam h i j) * (ENNReal.ofReal d) ^ n := by
        rw [Finset.sum_mul]
    _ = (ENNReal.ofReal d) ^ n := by rw [channelPMF_tsum, one_mul]
theorem sum_channelPMF_mul_le (lam : ℝ) (h : Admissible lam) (i : Spin)
    (X : Spin → ENNReal) (M : ENNReal) (hX : ∀ j, X j ≤ M) :
    (∑ j : Spin, channelPMF lam h i j * X j) ≤ M := by
  calc (∑ j : Spin, channelPMF lam h i j * X j)
      ≤ ∑ j : Spin, channelPMF lam h i j * M := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul' (le_refl _) (hX j)
    _ = (∑ j : Spin, channelPMF lam h i j) * M := by rw [Finset.sum_mul]
    _ = M := by rw [channelPMF_tsum, one_mul]
theorem poisC_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisC d hd lam h 0 i = 1 := by
  unfold poisC poissonLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * (totalCensus 0 o * totalCensus 0 o)) = 1
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [totalCensus]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem ofReal_sq_mul_pow_pair (d : ℝ) (hd : 0 ≤ d) (n : ℕ) :
    ENNReal.ofReal (d ^ 2) * (ENNReal.ofReal d ^ n * ENNReal.ofReal d ^ n)
      = ENNReal.ofReal (d ^ 2 * d ^ (2 * n)) := by
  have h1 : ENNReal.ofReal d ^ n * ENNReal.ofReal d ^ n = ENNReal.ofReal (d ^ (2 * n)) := by
    rw [← pow_add, ← ENNReal.ofReal_pow hd]
    congr 1
    ring
  rw [h1]
  exact (ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ d ^ 2)).symm
theorem poisC_bound (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    poisC d hd lam h n i ≤ ENNReal.ofReal ((d + 1) ^ (2 * n)) := by
  induction n generalizing i with
  | zero =>
      rw [poisC_zero]
      rw [show 2 * 0 = 0 from rfl, pow_zero, ENNReal.ofReal_one]
  | succ n ih =>
      rw [poisC_rec]
      have hS : (∑ j : Spin, channelPMF lam h i j * poisC d hd lam h n j)
          ≤ ENNReal.ofReal ((d + 1) ^ (2 * n)) :=
        sum_channelPMF_mul_le lam h i (fun j => poisC d hd lam h n j) _ ih
      have hT := channelPMF_sum_mul_const d hd lam h n i
      calc ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisC d hd lam h n j +
          ENNReal.ofReal (d ^ 2) * ((∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j) *
            (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j))
          ≤ ENNReal.ofReal d * ENNReal.ofReal ((d + 1) ^ (2 * n)) +
            ENNReal.ofReal (d ^ 2) * (ENNReal.ofReal d ^ n * ENNReal.ofReal d ^ n) := by
              rw [hT]
              exact add_le_add (mul_le_mul' (le_refl _) hS) (le_refl _)
        _ = ENNReal.ofReal (d * (d + 1) ^ (2 * n)) + ENNReal.ofReal (d ^ 2 * d ^ (2 * n)) := by
              rw [← ENNReal.ofReal_mul hd, ofReal_sq_mul_pow_pair d hd n]
        _ = ENNReal.ofReal (d * (d + 1) ^ (2 * n) + d ^ 2 * d ^ (2 * n)) := by
              rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ ENNReal.ofReal ((d + 1) ^ (2 * (n + 1))) := by
              apply ENNReal.ofReal_le_ofReal
              have hX : d ^ (2 * n) ≤ (d + 1) ^ (2 * n) :=
                pow_le_pow_left₀ hd (by linarith) (2 * n)
              have hX0 : (0:ℝ) ≤ (d + 1) ^ (2 * n) := by positivity
              have hdd : d + d ^ 2 ≤ (d + 1) ^ 2 := by nlinarith
              calc d * (d + 1) ^ (2 * n) + d ^ 2 * d ^ (2 * n)
                  ≤ d * (d + 1) ^ (2 * n) + d ^ 2 * (d + 1) ^ (2 * n) := by
                    linarith [mul_le_mul_of_nonneg_left hX (by positivity : (0:ℝ) ≤ d^2)]
                _ = (d + d ^ 2) * (d + 1) ^ (2 * n) := by ring
                _ ≤ (d + 1) ^ 2 * (d + 1) ^ (2 * n) :=
                    mul_le_mul_of_nonneg_right hdd hX0
                _ = (d + 1) ^ (2 * (n + 1)) := by
                    rw [show 2 * (n + 1) = 2 + 2 * n by ring, pow_add]
theorem poisC_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : poisC d hd lam h n i ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (poisC_bound d hd hd1 lam h n i)
theorem poisA_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : poisA d hd lam h n i ≠ ⊤ :=
  ne_top_of_le_ne_top (poisC_ne_top d hd hd1 lam h n i) (poisA_le_poisC d hd lam h n i)
theorem poisB_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : poisB d hd lam h n i ≠ ⊤ :=
  ne_top_of_le_ne_top (poisC_ne_top d hd hd1 lam h n i) (poisB_le_poisC d hd lam h n i)
theorem toReal_sum_channelPMF_mul (lam : ℝ) (h : Admissible lam) (i : Spin)
    (X : Spin → ENNReal) (hX : ∀ j, X j ≠ ⊤) :
    (∑ j : Spin, channelPMF lam h i j * X j).toReal
      = ∑ j : Spin, channel lam i j * (X j).toReal := by
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [ENNReal.toReal_mul, toReal_channelPMF]
  · intro j _
    exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (hX j)
noncomputable def poisAM (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j
noncomputable def poisAT (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) : ENNReal :=
  ∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j
theorem poisAM_ne_top (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisAM d hd lam h n i ≠ ⊤ := by
  unfold poisAM
  rw [ENNReal.sum_ne_top]
  intro j _
  exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisM_ne_top d hd lam h n j)
theorem poisAT_ne_top (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisAT d hd lam h n i ≠ ⊤ := by
  unfold poisAT
  rw [ENNReal.sum_ne_top]
  intro j _
  exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisT_ne_top d hd lam h n j)
theorem poisAT_eq (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisAT d hd lam h n i = (ENNReal.ofReal d) ^ n := by
  unfold poisAT
  calc (∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j)
      = ∑ j : Spin, channelPMF lam h i j * (ENNReal.ofReal d) ^ n := by
        apply Finset.sum_congr rfl
        intro j _; rw [poisT_eq]
    _ = (∑ j : Spin, channelPMF lam h i j) * (ENNReal.ofReal d) ^ n := by
        rw [Finset.sum_mul]
    _ = (ENNReal.ofReal d) ^ n := by rw [channelPMF_tsum, one_mul]
theorem poisAT_toReal (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (poisAT d hd lam h n i).toReal = d ^ n := by
  rw [poisAT_eq, ENNReal.toReal_pow, ENNReal.toReal_ofReal hd]
theorem poisAM_toReal (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (poisAM d hd lam h n i).toReal = d ^ n * (1 / 3 + lam ^ (n + 1) * eSpin i) := by
  unfold poisAM
  rw [toReal_sum_channelPMF_mul lam h i (fun j => poisM d hd lam h n j)
    (fun j => poisM_ne_top d hd lam h n j)]
  have h1 : (∑ j : Spin, channel lam i j * (1 / 3 : ℝ)) = 1 / 3 := by
    calc ∑ j : Spin, channel lam i j * (1 / 3 : ℝ)
        = (∑ j : Spin, channel lam i j) * (1 / 3) := by rw [Finset.sum_mul]
      _ = 1 / 3 := by rw [channel_sum]; ring
  have h3 : (∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)) = lam ^ n * (lam * eSpin i) := by
    calc ∑ j : Spin, channel lam i j * (lam ^ n * eSpin j)
        = ∑ j : Spin, lam ^ n * (channel lam i j * eSpin j) := by
          apply Finset.sum_congr rfl
          intro j _; ring
      _ = lam ^ n * ∑ j : Spin, channel lam i j * eSpin j := by rw [Finset.mul_sum]
      _ = lam ^ n * (lam * eSpin i) := by rw [channel_mul_eSpin]
  calc (∑ j : Spin, channel lam i j * (poisM d hd lam h n j).toReal)
      = ∑ j : Spin, channel lam i j * (d ^ n * (1 / 3 + lam ^ n * eSpin j)) := by
        apply Finset.sum_congr rfl
        intro j _; rw [poisM_formula]
    _ = d ^ n * ∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
    _ = d ^ n * (1 / 3 + lam ^ (n + 1) * eSpin i) := by
        congr 1
        rw [show (∑ j : Spin, channel lam i j * (1 / 3 + lam ^ n * eSpin j)) =
            ∑ j : Spin, (channel lam i j * (1 / 3 : ℝ) + channel lam i j * (lam ^ n * eSpin j)) by
          apply Finset.sum_congr rfl
          intro j _; ring]
        rw [Finset.sum_add_distrib, h1, h3, pow_succ]
        ring
theorem poisA_finset_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (∑ j : Spin, channelPMF lam h i j * poisA d hd lam h n j) ≠ ⊤ := by
  rw [ENNReal.sum_ne_top]
  intro j _
  exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisA_ne_top d hd hd1 lam h n j)
theorem poisB_finset_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (∑ j : Spin, channelPMF lam h i j * poisB d hd lam h n j) ≠ ⊤ := by
  rw [ENNReal.sum_ne_top]
  intro j _
  exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisB_ne_top d hd hd1 lam h n j)
theorem poisC_finset_ne_top (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (∑ j : Spin, channelPMF lam h i j * poisC d hd lam h n j) ≠ ⊤ := by
  rw [ENNReal.sum_ne_top]
  intro j _
  exact ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j) (poisC_ne_top d hd hd1 lam h n j)
theorem poisAM_unfold (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisAM d hd lam h n i = ∑ j : Spin, channelPMF lam h i j * poisM d hd lam h n j := rfl
theorem poisAT_unfold (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisAT d hd lam h n i = ∑ j : Spin, channelPMF lam h i j * poisT d hd lam h n j := rfl
theorem poisA_toReal_rec (d : ℝ) (hd0 : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (poisA d hd0 lam h (n + 1) i).toReal =
      d * ∑ j : Spin, channel lam i j * (poisA d hd0 lam h n j).toReal +
        d ^ 2 * ((poisAM d hd0 lam h n i).toReal * (poisAM d hd0 lam h n i).toReal) := by
  rw [poisA_rec]
  change (ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisA d hd0 lam h n j +
      ENNReal.ofReal (d ^ 2) * (poisAM d hd0 lam h n i * poisAM d hd0 lam h n i)).toReal =
    d * ∑ j : Spin, channel lam i j * (poisA d hd0 lam h n j).toReal +
      d ^ 2 * ((poisAM d hd0 lam h n i).toReal * (poisAM d hd0 lam h n i).toReal)
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (poisA_finset_ne_top d hd0 hd1 lam h n i))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (poisAM_ne_top d hd0 lam h n i) (poisAM_ne_top d hd0 lam h n i))),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hd0, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ d ^ 2),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j)
      (poisA_ne_top d hd0 hd1 lam h n j))]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_mul, toReal_channelPMF]
theorem poisB_toReal_rec (d : ℝ) (hd0 : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (poisB d hd0 lam h (n + 1) i).toReal =
      d * ∑ j : Spin, channel lam i j * (poisB d hd0 lam h n j).toReal +
        d ^ 2 * ((poisAM d hd0 lam h n i).toReal * (poisAT d hd0 lam h n i).toReal) := by
  rw [poisB_rec]
  change (ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisB d hd0 lam h n j +
      ENNReal.ofReal (d ^ 2) * (poisAM d hd0 lam h n i * poisAT d hd0 lam h n i)).toReal =
    d * ∑ j : Spin, channel lam i j * (poisB d hd0 lam h n j).toReal +
      d ^ 2 * ((poisAM d hd0 lam h n i).toReal * (poisAT d hd0 lam h n i).toReal)
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (poisB_finset_ne_top d hd0 hd1 lam h n i))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (poisAM_ne_top d hd0 lam h n i) (poisAT_ne_top d hd0 lam h n i))),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hd0, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ d ^ 2),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j)
      (poisB_ne_top d hd0 hd1 lam h n j))]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_mul, toReal_channelPMF]
theorem poisC_toReal_rec (d : ℝ) (hd0 : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam)
    (n : ℕ) (i : Spin) :
    (poisC d hd0 lam h (n + 1) i).toReal =
      d * ∑ j : Spin, channel lam i j * (poisC d hd0 lam h n j).toReal +
        d ^ 2 * ((poisAT d hd0 lam h n i).toReal * (poisAT d hd0 lam h n i).toReal) := by
  rw [poisC_rec]
  change (ENNReal.ofReal d * ∑ j : Spin, channelPMF lam h i j * poisC d hd0 lam h n j +
      ENNReal.ofReal (d ^ 2) * (poisAT d hd0 lam h n i * poisAT d hd0 lam h n i)).toReal =
    d * ∑ j : Spin, channel lam i j * (poisC d hd0 lam h n j).toReal +
      d ^ 2 * ((poisAT d hd0 lam h n i).toReal * (poisAT d hd0 lam h n i).toReal)
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (poisC_finset_ne_top d hd0 hd1 lam h n i))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (poisAT_ne_top d hd0 lam h n i) (poisAT_ne_top d hd0 lam h n i))),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hd0, ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ d ^ 2),
    ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top ((channelPMF lam h i).apply_ne_top j)
      (poisC_ne_top d hd0 hd1 lam h n j))]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_mul, toReal_channelPMF]
noncomputable def poisV (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) : ℝ :=
  (poisA d hd lam h n i).toReal - (2 / 3) * (poisB d hd lam h n i).toReal
    + (1 / 9) * (poisC d hd lam h n i).toReal
theorem cross_term_eq (d lam : ℝ) (n : ℕ) (e : ℝ) :
    d ^ 2 * (d ^ n * (1 / 3 + lam ^ (n + 1) * e)) ^ 2
      - (2 / 3) * (d ^ 2 * (d ^ n * (1 / 3 + lam ^ (n + 1) * e)) * d ^ n)
      + (1 / 9) * (d ^ 2 * (d ^ n) ^ 2) = ((d * lam) ^ 2) ^ (n + 1) * e ^ 2 := by
  have hpow : ((d * lam) ^ 2) ^ (n + 1) = (d * lam) ^ (2 * n) * ((d * lam) ^ 2) := by
    rw [pow_succ]
    congr 1
    rw [← pow_mul]
  rw [hpow, mul_pow, mul_pow, mul_pow]
  have hd2 : d ^ (2 * n) = d ^ n * d ^ n := by
    rw [show 2 * n = n + n by ring, pow_add]
  rw [hd2]
  ring
theorem poisV_step_alg (d lam : ℝ) (n : ℕ) (e A B C : ℝ) :
    (d * A + d ^ 2 * ((d ^ n * (1 / 3 + lam ^ (n + 1) * e)) *
        (d ^ n * (1 / 3 + lam ^ (n + 1) * e))))
      - (2 / 3) * (d * B + d ^ 2 * ((d ^ n * (1 / 3 + lam ^ (n + 1) * e)) * d ^ n))
      + (1 / 9) * (d * C + d ^ 2 * (d ^ n * d ^ n))
    = d * (A - (2 / 3) * B + (1 / 9) * C)
      + ((d * lam) ^ 2) ^ (n + 1) * e ^ 2 := by
  have h := cross_term_eq d lam n e
  linarith
theorem poisA_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisA d hd lam h 0 i = (if i = (1 : Spin) then (1 : ENNReal) else 0) := by
  unfold poisA poissonLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * (census 0 o * census 0 o)) = _
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [census]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem poisB_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisB d hd lam h 0 i = (if i = (1 : Spin) then (1 : ENNReal) else 0) := by
  unfold poisB poissonLaw observedLaw
  change (∑' o : Spin, (PMF.pure i : PMF Spin) o * (census 0 o * totalCensus 0 o)) = _
  rw [tsum_eq_single i]
  · rw [PMF.pure_apply_self]
    simp [census, totalCensus]
  · intro o ho
    rw [PMF.pure_apply, if_neg ho]
    simp
theorem poisV_zero (d : ℝ) (hd : 0 ≤ d) (lam : ℝ) (h : Admissible lam) (i : Spin) :
    poisV d hd lam h 0 i = eSpin i ^ 2 := by
  rw [poisV, poisA_zero, poisB_zero, poisC_zero]
  fin_cases i <;> norm_num [eSpin]
theorem sum_channel_mul_real (lam : ℝ) (i : Spin) (a b c : Spin → ℝ) :
    (∑ j : Spin, channel lam i j * a j) - (2 / 3) * (∑ j : Spin, channel lam i j * b j)
      + (1 / 9) * (∑ j : Spin, channel lam i j * c j)
    = ∑ j : Spin, channel lam i j * (a j - (2 / 3) * b j + (1 / 9) * c j) := by
  rw [Finset.mul_sum (Finset.univ) (fun j => channel lam i j * b j) (2/3 : ℝ),
    Finset.mul_sum (Finset.univ) (fun j => channel lam i j * c j) (1/9 : ℝ)]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring
theorem poisV_rec (d : ℝ) (hd0 : 0 ≤ d) (hd1 : 1 ≤ d)
    (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisV d hd0 lam h (n + 1) i =
      d * ∑ j : Spin, channel lam i j * poisV d hd0 lam h n j
        + ((d * lam) ^ 2) ^ (n + 1) * eSpin i ^ 2 := by
  rw [poisV, poisA_toReal_rec d hd0 hd1 lam h n i,
    poisB_toReal_rec d hd0 hd1 lam h n i, poisC_toReal_rec d hd0 hd1 lam h n i,
    poisAM_toReal d hd0 lam h n i, poisAT_toReal d hd0 lam h n i]
  have hAB : (∑ j : Spin, channel lam i j * (poisA d hd0 lam h n j).toReal) -
      (2 / 3) * (∑ j : Spin, channel lam i j * (poisB d hd0 lam h n j).toReal) +
      (1 / 9) * (∑ j : Spin, channel lam i j * (poisC d hd0 lam h n j).toReal)
      = ∑ j : Spin, channel lam i j * poisV d hd0 lam h n j := by
    rw [sum_channel_mul_real]
    apply Finset.sum_congr rfl
    intro j _
    rw [poisV]
  rw [poisV_step_alg d lam n (eSpin i) _ _ _, hAB]
theorem tsum_three {α : Type*} (a b c : α → ℝ) (ha : Summable a) (hb : Summable b) (hc : Summable c) :
    (∑' x, (a x - (2 / 3) * b x + (1 / 9) * c x))
      = (∑' x, a x) - (2 / 3) * (∑' x, b x) + (1 / 9) * (∑' x, c x) := by
  have hb' : Summable fun x => (2 / 3 : ℝ) * b x := hb.mul_left _
  have hc' : Summable fun x => (1 / 9 : ℝ) * c x := hc.mul_left _
  rw [Summable.tsum_add (f := fun x => a x - (2 / 3) * b x) (g := fun x => (1/9) * c x)
      (ha.sub hb') hc']
  rw [Summable.tsum_sub (f := a) (g := fun x => (2 / 3) * b x) ha hb']
  rw [tsum_mul_left (f := b) (a := (2/3:ℝ)), tsum_mul_left (f := c) (a := (1/9:ℝ))]
theorem leafSq_pointwise (n : ℕ) (o : Observation n) :
    (leafSum eSpin n o) ^ 2 =
      (census n o * census n o).toReal
        - (2 / 3) * (census n o * totalCensus n o).toReal
        + (1 / 9) * (totalCensus n o * totalCensus n o).toReal := by
  rw [leafSum_eSpin_eq, ENNReal.toReal_mul, ENNReal.toReal_mul]
  have h : (totalCensus n o * totalCensus n o).toReal = (totalCensus n o).toReal ^ 2 := by
    rw [ENNReal.toReal_mul]; ring
  rw [h]; ring
theorem summable_A (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * (census n o * census n o).toReal) :=
  TheoremOS.Probability.summable_toReal_mul_toReal _ _
    (poisA_ne_top d hd hd1 lam h n i)
theorem summable_B (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * (census n o * totalCensus n o).toReal) :=
  TheoremOS.Probability.summable_toReal_mul_toReal _ _
    (poisB_ne_top d hd hd1 lam h n i)
theorem summable_C (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * (totalCensus n o * totalCensus n o).toReal) :=
  TheoremOS.Probability.summable_toReal_mul_toReal _ _
    (poisC_ne_top d hd hd1 lam h n i)
theorem tsum_A (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (∑' o : Observation n,
      (poissonLaw d hd lam h n i o).toReal * (census n o * census n o).toReal)
      = (poisA d hd lam h n i).toReal :=
  TheoremOS.Probability.tsum_toReal_mul_toReal _ _ (poisA_ne_top d hd hd1 lam h n i)
theorem tsum_B (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (∑' o : Observation n,
      (poissonLaw d hd lam h n i o).toReal * (census n o * totalCensus n o).toReal)
      = (poisB d hd lam h n i).toReal :=
  TheoremOS.Probability.tsum_toReal_mul_toReal _ _ (poisB_ne_top d hd hd1 lam h n i)
theorem tsum_C (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    (∑' o : Observation n,
      (poissonLaw d hd lam h n i o).toReal * (totalCensus n o * totalCensus n o).toReal)
      = (poisC d hd lam h n i).toReal :=
  TheoremOS.Probability.tsum_toReal_mul_toReal _ _ (poisC_ne_top d hd hd1 lam h n i)
theorem poisV_eq_leaf (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    poisV d hd lam h n i =
      ∑' o : Observation n,
        (poissonLaw d hd lam h n i o).toReal * (leafSum eSpin n o) ^ 2 := by
  have h1 := summable_A d hd hd1 lam h n i
  have h2 := summable_B d hd hd1 lam h n i
  have h3 := summable_C d hd hd1 lam h n i
  have h2' : Summable (fun o : Observation n =>
      (2 / 3) * ((poissonLaw d hd lam h n i o).toReal *
        (census n o * totalCensus n o).toReal)) := h2.mul_left _
  have h3' : Summable (fun o : Observation n =>
      (1 / 9) * ((poissonLaw d hd lam h n i o).toReal *
        (totalCensus n o * totalCensus n o).toReal)) := h3.mul_left _
  have hsub := h1.sub h2'
  have hall := hsub.add h3'
  have hcongr : (∑' o : Observation n,
        (poissonLaw d hd lam h n i o).toReal * (leafSum eSpin n o) ^ 2)
      = (∑' o : Observation n,
          ((poissonLaw d hd lam h n i o).toReal * (census n o * census n o).toReal
            - (2 / 3) * ((poissonLaw d hd lam h n i o).toReal
                * (census n o * totalCensus n o).toReal)
            + (1 / 9) * ((poissonLaw d hd lam h n i o).toReal
                * (totalCensus n o * totalCensus n o).toReal))) := by
    apply tsum_congr
    intro o
    rw [leafSq_pointwise]
    ring
  rw [hcongr, tsum_three _ _ _ h1 h2 h3, tsum_A d hd hd1 lam h n i,
    tsum_B d hd hd1 lam h n i, tsum_C d hd hd1 lam h n i, poisV]
theorem poisLeaf_summable (d : ℝ) (hd : 0 ≤ d) (hd1 : 1 ≤ d) (lam : ℝ) (h : Admissible lam) (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (poissonLaw d hd lam h n i o).toReal * (leafSum eSpin n o) ^ 2) := by
  have h1 := summable_A d hd hd1 lam h n i
  have h2 := summable_B d hd hd1 lam h n i
  have h3 := summable_C d hd hd1 lam h n i
  have h2' : Summable (fun o : Observation n =>
      (2 / 3) * ((poissonLaw d hd lam h n i o).toReal *
        (census n o * totalCensus n o).toReal)) := h2.mul_left _
  have h3' : Summable (fun o : Observation n =>
      (1 / 9) * ((poissonLaw d hd lam h n i o).toReal *
        (totalCensus n o * totalCensus n o).toReal)) := h3.mul_left _
  refine ((h1.sub h2').add h3').congr fun o => ?_
  rw [leafSq_pointwise]
  ring
theorem key_coeff (d lam : ℝ) (hd : 1 < d) (hcrit : 1 < d * lam ^ 2) :
    d * ((4 / 9) / (1 - 1 / (d * lam ^ 2))) + (4 / 9) * ((d * lam) ^ 2)
      = ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d * lam) ^ 2) := by
  set r : ℝ := d * lam ^ 2 with hr
  have hr1 : 1 < r := hcrit
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrne : r - 1 ≠ 0 := by intro h; nlinarith
  have hC : (4 / 9 : ℝ) / (1 - 1 / r) = (4 / 9) * r / (r - 1) := by
    have hr' : r ≠ 0 := ne_of_gt hr0
    field_simp
  have hs : (d * lam) ^ 2 = d * r := by rw [hr]; ring
  rw [hC, hs]
  field_simp
  ring
theorem C_mul_one_sub_q (d lam : ℝ) (hd : 1 < d) (hcrit : 1 < d * lam ^ 2) :
    ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * (1 - 1 / (d * lam ^ 2)) = 4 / 9 := by
  set r : ℝ := d * lam ^ 2 with hr
  have hr1 : 1 < r := hcrit
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hq : 0 < 1 - 1 / r := by
    have h : 1 / r < 1 := by rw [div_lt_one hr0]; linarith
    linarith
  have hqne : (1 - 1 / r) ≠ 0 := ne_of_gt hq
  rw [div_mul_cancel₀ _ hqne]
theorem poisV_bound (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) :
    ∀ (n : ℕ) (i : Spin),
      poisV d (le_trans (by norm_num) hd.le) lam h n i ≤
        ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d * lam) ^ 2) ^ n := by
  intro n
  set C : ℝ := (4 / 9) / (1 - 1 / (d * lam ^ 2)) with hCdef
  set s : ℝ := (d * lam) ^ 2 with hsdef
  have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_trans zero_lt_one hd)
  have hd1 : (1:ℝ) ≤ d := le_of_lt hd
  have hr0 : 0 < d * lam ^ 2 := lt_trans zero_lt_one hcrit
  have hq : 1 / (d * lam ^ 2) < 1 := by rw [div_lt_one hr0]; linarith
  have hqpos : 0 < 1 - 1 / (d * lam ^ 2) := by linarith
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hCq : C * (1 - 1 / (d * lam ^ 2)) = 4 / 9 := by
    rw [hCdef]; exact C_mul_one_sub_q d lam hd hcrit
  have hkey : d * C + (4 / 9) * s = C * s := by
    rw [hCdef, hsdef]; exact key_coeff d lam hd hcrit
  have hsnn : 0 ≤ s := by rw [hsdef]; positivity
  induction n with
  | zero =>
      intro i
      rw [poisV_zero]
      calc eSpin i ^ 2 ≤ 4 / 9 := eSpin_sq_le i
        _ = C * (1 - 1 / (d * lam ^ 2)) := hCq.symm
        _ ≤ C * 1 := by
            apply mul_le_mul_of_nonneg_left _ hCpos.le
            have hp : 0 ≤ 1 / (d * lam ^ 2) := by positivity
            linarith
        _ = C * s ^ 0 := by rw [pow_zero, mul_one]
  | succ n ih =>
      intro i
      rw [poisV_rec d hd0 hd1 lam h n i]
      have hrow : (∑ j : Spin, channel lam i j * (C * s ^ n)) = C * s ^ n := by
        rw [← Finset.sum_mul, channel_sum, one_mul]
      have hsn : 0 ≤ s ^ n := pow_nonneg hsnn n
      have hb1 : (∑ j : Spin, channel lam i j * poisV d hd0 lam h n j)
          ≤ C * s ^ n := by
        calc (∑ j : Spin, channel lam i j * poisV d hd0 lam h n j)
            ≤ ∑ j : Spin, channel lam i j * (C * s ^ n) := by
              apply Finset.sum_le_sum
              intro j _
              exact mul_le_mul_of_nonneg_left (ih j) (channel_nonneg h i j)
          _ = C * s ^ n := hrow
      have he : eSpin i ^ 2 ≤ 4 / 9 := eSpin_sq_le i
      have hs1 : 0 ≤ s ^ (n + 1) := pow_nonneg hsnn _
      calc d * (∑ j : Spin, channel lam i j * poisV d hd0 lam h n j)
            + s ^ (n + 1) * eSpin i ^ 2
          ≤ d * (C * s ^ n) + s ^ (n + 1) * (4 / 9) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hb1 hd0
            · exact mul_le_mul_of_nonneg_left he hs1
        _ = s ^ n * (d * C + (4 / 9) * s) := by
            rw [pow_succ]; ring
        _ = s ^ n * (C * s) := by rw [hkey]
        _ = C * s ^ (n + 1) := by rw [pow_succ]; ring
theorem poissonLeaf_second_moment (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) :
    ((∀ (n : ℕ) (i : Spin),
        Summable (fun o : Observation n =>
          (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
            (leafSum eSpin n o) ^ 2)) ∧
      (∀ (n : ℕ) (i : Spin),
        (∑' o : Observation n,
          (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
            (leafSum eSpin n o) ^ 2) ≤
          ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d : ℝ) * lam) ^ (2 * n))) := by
  have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_trans zero_lt_one hd)
  have hd1 : (1:ℝ) ≤ d := le_of_lt hd
  refine ⟨fun n i => poisLeaf_summable d hd0 hd1 lam h n i, fun n i => ?_⟩
  rw [← poisV_eq_leaf d hd0 hd1 lam h n i]
  rw [show ((d : ℝ) * lam) ^ (2 * n) = ((d * lam) ^ 2) ^ n from by rw [← pow_mul]]
  exact poisV_bound d hd lam h hcrit n i
theorem poissonLeaf_moments (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) :
    (∀ (n : ℕ) (i : Spin),
        (∑' o : Observation n,
          (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal * leafSum eSpin n o)
          = ((d : ℝ) * lam) ^ n * eSpin i)
      ∧ ((∀ (n : ℕ) (i : Spin), Summable (fun o : Observation n =>
            (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
              (leafSum eSpin n o) ^ 2))
        ∧ (∀ (n : ℕ) (i : Spin),
            (∑' o : Observation n,
              (poissonLaw d (le_trans (by norm_num) hd.le) lam h n i o).toReal *
                (leafSum eSpin n o) ^ 2) ≤
              ((4 / 9) / (1 - 1 / (d * lam ^ 2))) * ((d : ℝ) * lam) ^ (2 * n))) := by
  exact ⟨poissonLeaf_first_moment d hd lam h hcrit,
    poissonLeaf_second_moment d hd lam h hcrit⟩
theorem regular_supercritical (b : ℕ) (hb : 2 ≤ b) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < (b : ℝ) * lam ^ 2) : Reconstructs (regularAdvantage b lam h) := by
  set r : ℝ := (b : ℝ) * lam ^ 2 with hr
  set s : ℝ := ((b : ℝ) * lam) ^ 2 with hs
  set Q : ℝ := 4 * r / (9 * (r - 1)) with hQ
  have hr1 : 1 < r := hcrit
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hrm1 : 0 < r - 1 := by linarith
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hs_pos : 0 < s := by
    rw [hs]
    apply sq_pos_of_ne_zero
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hb)
    have hlam : lam ≠ 0 := by
      intro hz
      rw [hr, hz] at hr0
      simp at hr0
    exact mul_ne_zero hbpos.ne' hlam
  have hTV : ∀ n : ℕ, (1 : ℝ) / (4 * Q) ≤
      TheoremOS.Probability.pmfTV (regularLaw b lam h n (1 : Spin)) (regularLaw b lam h n (0 : Spin)) := by
    intro n
    set p : PMF (Observation n) := regularLaw b lam h n (1 : Spin) with hp_def
    set q : PMF (Observation n) := regularLaw b lam h n (0 : Spin) with hq_def
    set S : Observation n → ℝ := fun o => (census n o).toReal with hS_def
    have hp_sum : Summable fun a => (p a).toReal * S a ^ 2 := by
      have hA : (∑' a : Observation n, p a * (census n a * census n a)) ≠ ⊤ := by
        have := regA_ne_top b lam h n (1 : Spin)
        simpa [regA, p] using this
      have hsA := TheoremOS.Probability.summable_toReal_mul_toReal p
        (fun a => census n a * census n a) hA
      simpa [S, pow_two, ENNReal.toReal_mul] using hsA
    have hq_sum : Summable fun a => (q a).toReal * S a ^ 2 := by
      have hA : (∑' a : Observation n, q a * (census n a * census n a)) ≠ ⊤ := by
        have := regA_ne_top b lam h n (0 : Spin)
        simpa [regA, q] using this
      have hsA := TheoremOS.Probability.summable_toReal_mul_toReal q
        (fun a => census n a * census n a) hA
      simpa [S, pow_two, ENNReal.toReal_mul] using hsA
    have hM1 : (∑' o : Observation n, (p o).toReal * S o) =
        (regM b lam h n (1 : Spin)).toReal := by
      rw [show (∑' o : Observation n, (p o).toReal * S o) =
          ∑' o : Observation n, (p o).toReal * (census n o).toReal by rfl]
      rw [TheoremOS.Probability.tsum_toReal_mul_toReal p (fun o => census n o)
        (by simpa [p, regM] using regM_ne_top b lam h n (1 : Spin))]
      simp [p, regM]
    have hM0 : (∑' o : Observation n, (q o).toReal * S o) =
        (regM b lam h n (0 : Spin)).toReal := by
      rw [show (∑' o : Observation n, (q o).toReal * S o) =
          ∑' o : Observation n, (q o).toReal * (census n o).toReal by rfl]
      rw [TheoremOS.Probability.tsum_toReal_mul_toReal q (fun o => census n o)
        (by simpa [q, regM] using regM_ne_top b lam h n (0 : Spin))]
      simp [q, regM]
    have hmean : (∑' o : Observation n, (p o).toReal * S o) -
        (∑' o : Observation n, (q o).toReal * S o) = ((b : ℝ) * lam) ^ n := by
      rw [hM1, hM0, regM_formula, regM_formula]
      have hsub : eSpin (1 : Spin) - eSpin (0 : Spin) = 1 := eSpin_one_sub_zero
      have : (b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin 1) -
          (b : ℝ) ^ n * (1 / 3 + lam ^ n * eSpin 0) =
          (b : ℝ) ^ n * lam ^ n * (eSpin 1 - eSpin 0) := by ring
      rw [this, hsub, mul_one, mul_pow]
    have hsquare : ((∑' o : Observation n, (p o).toReal * S o) -
        (∑' o : Observation n, (q o).toReal * S o)) ^ 2 = s ^ n := by
      rw [hmean, hs]
      exact (pow_right_comm _ 2 n).symm
    have hW1 : (∑' o : Observation n, (p o).toReal * (S o - regC b n) ^ 2) =
        regW b lam h n (1 : Spin) := by
      simp [regW, p, S]
    have hW0 : (∑' o : Observation n, (q o).toReal * (S o - regC b n) ^ 2) =
        regW b lam h n (0 : Spin) := by
      simp [regW, q, S]
    have hWsum : (∑' o : Observation n, (p o).toReal * (S o - regC b n) ^ 2) +
        (∑' o : Observation n, (q o).toReal * (S o - regC b n) ^ 2) ≤
        2 * (Q * s ^ n) := by
      rw [hW1, hW0]
      have h1 : regW b lam h n (1 : Spin) ≤ Q * s ^ n := by
        simpa [Q, s, r, hQ, hs, hr] using regW_bound b hb lam h hcrit n (1 : Spin)
      have h0 : regW b lam h n (0 : Spin) ≤ Q * s ^ n := by
        simpa [Q, s, r, hQ, hs, hr] using regW_bound b hb lam h hcrit n (0 : Spin)
      linarith
    have hmain := TheoremOS.Probability.sq_sub_le_pmfTV_mul_centred p q S (regC b n)
      hp_sum hq_sum
    have hle : s ^ n ≤ 2 * TheoremOS.Probability.pmfTV p q * (2 * (Q * s ^ n)) := by
      calc
        s ^ n = ((∑' o : Observation n, (p o).toReal * S o) -
            (∑' o : Observation n, (q o).toReal * S o)) ^ 2 := hsquare.symm
        _ ≤ 2 * TheoremOS.Probability.pmfTV p q * ((∑' o : Observation n,
              (p o).toReal * (S o - regC b n) ^ 2) +
              (∑' o : Observation n, (q o).toReal * (S o - regC b n) ^ 2)) := hmain
        _ ≤ 2 * TheoremOS.Probability.pmfTV p q * (2 * (Q * s ^ n)) := by
              apply mul_le_mul_of_nonneg_left hWsum
              have htv0 : 0 ≤ TheoremOS.Probability.pmfTV p q := TheoremOS.Probability.pmfTV_nonneg p q
              positivity
    have hspos : 0 < s ^ n := pow_pos hs_pos n
    have hquad : 1 ≤ 4 * Q * TheoremOS.Probability.pmfTV p q := by
      have hle' : s ^ n ≤ (4 * Q * s ^ n) * TheoremOS.Probability.pmfTV p q := by
        calc
          s ^ n ≤ 2 * TheoremOS.Probability.pmfTV p q * (2 * (Q * s ^ n)) := hle
          _ = (4 * Q * s ^ n) * TheoremOS.Probability.pmfTV p q := by ring
      have hle2 : s ^ n * 1 ≤ s ^ n * (4 * Q * TheoremOS.Probability.pmfTV p q) := by
        calc
          s ^ n * 1 = s ^ n := by ring
          _ ≤ (4 * Q * s ^ n) * TheoremOS.Probability.pmfTV p q := hle'
          _ = s ^ n * (4 * Q * TheoremOS.Probability.pmfTV p q) := by ring
      exact (mul_le_mul_iff_of_pos_left hspos).mp hle2
    have htv : (1 : ℝ) / (4 * Q) ≤ TheoremOS.Probability.pmfTV p q := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Q)]
      simpa [mul_comm] using hquad
    simpa [p, q] using htv
  have hAdv : ∀ n : ℕ, (1 : ℝ) / (12 * Q) ≤
      TheoremOS.Probability.reconAdvantage (regularLaw b lam h n) := by
    intro n
    have htv := hTV n
    have hcard := TheoremOS.Probability.pmfTV_le_card_mul_reconAdvantage
      (regularLaw b lam h n) (1 : Spin) (0 : Spin)
    have hcard3 : (Fintype.card Spin : ℝ) = 3 := by simp
    rw [hcard3] at hcard
    have h1 : (1 : ℝ) / (4 * Q) ≤ 3 * TheoremOS.Probability.reconAdvantage
        (regularLaw b lam h n) := htv.trans hcard
    have heq : (1 : ℝ) / (4 * Q) = 3 * (1 / (12 * Q)) := by
      field_simp
      ring
    rw [heq] at h1
    exact (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 3)).mp h1
  have hbc := isBroadcastLaw_observedLaw (PMF.pure b) lam h
  have hiff := hbc.exists_pos_tendsto_iff
    (leaf := fun i : Spin => i) (up := fun _ s => s) (law := observedLaw (PMF.pure b) lam h)
    (fun _ _ hij => hij) (fun _ _ _ hij => hij)
  have hpos : ∃ ε, 0 < ε ∧ ∀ n : ℕ,
      ε ≤ TheoremOS.Probability.reconAdvantage (observedLaw (PMF.pure b) lam h n) := by
    refine ⟨1 / (12 * Q), by positivity, ?_⟩
    intro n
    simpa [regularLaw] using hAdv n
  rcases hiff.mpr hpos with ⟨L, hL, hlim⟩
  refine ⟨L, hL, ?_⟩
  have hfun : regularAdvantage b lam h = fun n =>
      TheoremOS.Probability.reconAdvantage (observedLaw (PMF.pure b) lam h n) := by
    funext n
    simp only [regularAdvantage, regularLaw]
    exact advantage_eq_reconAdvantage (regularLaw b lam h n)
  rw [hfun]
  exact hlim
theorem poisson_supercritical (d : ℝ) (hd : 1 < d) (lam : ℝ) (h : Admissible lam)
    (hcrit : 1 < d * lam ^ 2) : Reconstructs (poissonAdvantage d hd lam h) :=
  poisson_reconstructs_of_leaf_moments d hd lam h hcrit
    (poissonLeaf_first_moment d hd lam h hcrit)
    (poissonLeaf_second_moment d hd lam h hcrit)

end ThreeState

end OAI
