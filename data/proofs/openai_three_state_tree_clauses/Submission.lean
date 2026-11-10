import Submission.Library.TheoremOS.Probability.TreeReconstruction
import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter

namespace ThreeState.TreeClauses

abbrev Spin := Fin 3

def Admissible (lam : ℝ) : Prop := -(1 / 2 : ℝ) ≤ lam ∧ lam ≤ 1

def channelWeight (lam : ℝ) (i j : Spin) : ℝ :=
  if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3

lemma channelWeight_nonneg {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    0 ≤ channelWeight lam i j := by
  unfold channelWeight
  split_ifs <;> dsimp [Admissible] at hlam <;> linarith [hlam.1, hlam.2]

lemma channelWeight_sum (lam : ℝ) (i : Spin) : ∑ j, channelWeight lam i j = 1 := by
  fin_cases i <;> simp [channelWeight, Fin.sum_univ_three] <;> ring

lemma channelWeight_centred_eigen (lam : ℝ) (i : Spin) :
    (∑ j : Spin, channelWeight lam i j *
      ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))
      = lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) := by
  fin_cases i <;> simp [channelWeight, Fin.sum_univ_three] <;> ring
def channel (lam : ℝ) (hlam : Admissible lam) (i : Spin) : PMF Spin :=
  PMF.ofFintype (fun j ↦ ENNReal.ofReal (channelWeight lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ channelWeight_nonneg hlam i j),
      channelWeight_sum]
    norm_num)

def Observation : ℕ → Type
  | 0 => Spin
  | n + 1 => Multiset (Observation n)

def iidList {α : Type} (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => p.bind fun x ↦ (iidList p n).map (List.cons x)

def observationLaw (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Spin → PMF (Observation ℓ)
  | 0, i => PMF.pure i
  | ℓ + 1, i => offspring.bind fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs ↦ (xs : Multiset (Observation ℓ)))

def jointWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) (o : Observation ℓ) : ℝ≥0∞ :=
  (1 / 3 : ℝ≥0∞) * observationLaw lam hlam offspring ℓ i o

def marginalWeight (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) : ℝ≥0∞ :=
  ∑ i, jointWeight lam hlam offspring ℓ i o

def posterior (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (o : Observation ℓ) (i : Spin) : ℝ :=
  (jointWeight lam hlam offspring ℓ i o / marginalWeight lam hlam offspring ℓ o).toReal

def advantage (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (ℓ : ℕ) : ℝ :=
  ∑' o : Observation ℓ, (marginalWeight lam hlam offspring ℓ o).toReal *
    ((∑ i : Spin, |posterior lam hlam offspring ℓ o i - (1 / 3 : ℝ)|) / 2)

def Reconstructs (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Tendsto (advantage lam hlam offspring) atTop (nhds a)

def censusState : (n : ℕ) → Observation n → ℝ≥0∞ :=
  Nat.rec (fun i : Spin => if i = (0 : Spin) then 1 else 0)
    (fun _ ih s => (s.map ih).sum)
theorem censusState_succ (n : ℕ) (s : Multiset (Observation n)) :
    censusState (n + 1) s = (s.map (censusState n)).sum := rfl
def totalCensus : (n : ℕ) → Observation n → ℝ≥0∞ :=
  Nat.rec (fun _ : Spin => 1) (fun _ ih s => (s.map ih).sum)
theorem totalCensus_succ (n : ℕ) (s : Multiset (Observation n)) :
    totalCensus (n + 1) s = (s.map (totalCensus n)).sum := rfl
theorem exists_census_pair :
    ∃ X M : (n : ℕ) → Observation n → ℝ≥0∞,
      (∀ (n : ℕ) (s : Multiset (Observation n)),
          X (n + 1) s = (s.map (X n)).sum) ∧
      (∀ (n : ℕ) (s : Multiset (Observation n)),
          M (n + 1) s = (s.map (M n)).sum) ∧
      (∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0) ∧
      (∀ i : Spin, M 0 i = 1) :=
  ⟨censusState, totalCensus, fun _ _ => rfl, fun _ _ => rfl,
    fun i => rfl, fun _ => rfl⟩
lemma multiset_sum_ne_top {α : Type} {f : α → ℝ≥0∞} (s : Multiset α)
    (h : ∀ a ∈ s, f a ≠ ∞) : (s.map f).sum ≠ ∞ := by
  induction s using Multiset.induction_on with
  | empty => exact ENNReal.zero_ne_top
  | cons a s ihs =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      refine ENNReal.add_ne_top.2 ⟨h a (by simp), ihs ?_⟩
      intro b hb
      exact h b (by simp [hb])
lemma censusState_zero_le (i : Spin) :
    (if i = (0 : Spin) then (1 : ℝ≥0∞) else 0) ≤ 1 := by
  split_ifs with h
  · exact le_rfl
  · exact zero_le_one' ℝ≥0∞
theorem census_finite_le (n : ℕ) (o : Observation n) :
    totalCensus n o ≠ ∞ ∧ censusState n o ≤ totalCensus n o := by
  revert o
  induction n with
  | zero =>
     intro o
     exact ⟨ENNReal.one_ne_top, censusState_zero_le o⟩
  | succ n ih =>
     intro o
     exact ⟨multiset_sum_ne_top _ (fun a _ => (ih a).1),
       Multiset.sum_map_le_sum_map (s := o)
         (fun a => censusState n a) (fun a => totalCensus n a) (fun a _ => (ih a).2)⟩
namespace Probability

def poissonWeight (rate : ℝ) (count : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ count / (count.factorial : ℝ)

lemma poissonWeight_nonneg {rate : ℝ} (hrate : 0 ≤ rate) (count : ℕ) :
    0 ≤ poissonWeight rate count := by
  unfold poissonWeight
  positivity

lemma poissonWeight_mass (rate : ℝ≥0) : HasSum (poissonWeight rate) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure rate

def _root_.OAI.ThreeState.TreeClauses.poissonPMF (rate : ℝ≥0) : PMF ℕ := by
  refine ⟨fun count ↦ ENNReal.ofReal (poissonWeight rate count), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← Real.toNNReal_one]
  exact (poissonWeight_mass rate).toNNReal (poissonWeight_nonneg rate.coe_nonneg)

end Probability

theorem isBroadcastLaw_observationLaw (lam : ℝ) (hlam : Admissible lam)
    (offspring : PMF ℕ) :
    TheoremOS.Probability.IsBroadcastLaw (O := Observation) (channel lam hlam) offspring
      (fun i : Spin => i) (fun _ s => s) (observationLaw lam hlam offspring) := by
  constructor
  · intro i
    rfl
  · intro ℓ i
    simp only [observationLaw]
    rw [← TheoremOS.Probability.iidList_eq_of_rec iidList (fun _ => rfl) (fun _ _ => rfl)]
    congr 1
    funext k
    exact TheoremOS.Probability.map_id_bind_pure_coe _

lemma admissible_pow_lower {lam : ℝ} (hlam : Admissible lam) (n : ℕ) :
    -(1 / 2 : ℝ) ≤ lam ^ n := by
  have h2 : lam ^ 2 ≤ 1 := by nlinarith [hlam.1, hlam.2]
  have h2nn : (0 : ℝ) ≤ lam ^ 2 := sq_nonneg lam
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, pow_add]
    nlinarith [mul_self_nonneg (lam ^ k)]
  · have hc1 : (lam ^ 2) ^ k ≤ 1 := pow_le_one₀ h2nn h2
    have he : lam ^ (2 * k + 1) = lam * (lam ^ 2) ^ k := by ring
    rw [hk, he]
    rcases lt_or_ge 0 lam with hpos | hneg
    · nlinarith [mul_nonneg hpos.le (pow_nonneg h2nn k)]
    · have hle := mul_le_mul_of_nonpos_left hc1 hneg
      nlinarith [hlam.1, hle]
lemma admissible_pow_upper {lam : ℝ} (hlam : Admissible lam) (n : ℕ) :
    lam ^ n ≤ 1 := by
  have habs : |lam| ≤ 1 := abs_le.2 ⟨by linarith [hlam.1], hlam.2⟩
  have hp : |lam ^ n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg lam) habs
  exact (le_abs_self (lam ^ n)).trans hp
lemma one_third_add_pow_mul_centred_nonneg {lam : ℝ} (hlam : Admissible lam) (n : ℕ)
    (j : Spin) :
    0 ≤ (1 / 3 : ℝ) + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) := by
  by_cases hj : j = (0 : Spin)
  · rw [ite_eq_left hj]
    linarith [admissible_pow_lower hlam n]
  · rw [ite_eq_right hj]
    linarith [admissible_pow_upper hlam n]
lemma channelWeight_sum_affine (lam : ℝ) (i : Spin) (n : ℕ) :
    (∑ j : Spin, channelWeight lam i j *
        ((1 / 3 : ℝ) + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)))
      = (1 / 3 : ℝ) +
        lam ^ (n + 1) * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) := by
  have hsplit : ∀ j : Spin, channelWeight lam i j *
        ((1 / 3 : ℝ) + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))
      = channelWeight lam i j * (1 / 3) +
        lam ^ n * (channelWeight lam i j *
          ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
    intro j; ring
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 : (∑ x : Spin, channelWeight lam i x * (1 / 3 : ℝ)) = 1 / 3 := by
    rw [← Finset.sum_mul, channelWeight_sum, one_mul]
  have h2 : (∑ x : Spin, lam ^ n * (channelWeight lam i x *
        ((if x = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)))
      = lam ^ n * (lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
    rw [← Finset.mul_sum, channelWeight_centred_eigen]
  rw [h1, h2]
  ring
theorem stateCensus_moment (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hm0 : 0 ≤ m) :
    ∀ (n : ℕ) (i : Spin),
      (∑' o : Observation n,
        observationLaw lam hlam offspring n i o * censusState n o) =
        ENNReal.ofReal (m ^ n *
          (1 / 3 + lam ^ n * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))) := by
  intro n
  induction n with
  | zero =>
      intro i
      change (∑' o : Spin, (PMF.pure i) o *
          (if o = (0 : Spin) then (1 : ℝ≥0∞) else 0)) =
        ENNReal.ofReal (m ^ 0 *
          (1 / 3 + lam ^ 0 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)))
      rw [TheoremOS.Probability.tsum_pure_mul]
      simp only [pow_zero, one_mul]
      by_cases hi : i = (0 : Spin)
      · rw [ite_eq_left hi, ite_eq_left hi]
        norm_num
      · rw [ite_eq_right hi, ite_eq_right hi]
        norm_num
  | succ n ih =>
      intro i
      have hb := (isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census
        (fun n : ℕ => censusState n) (fun n s => censusState_succ n s) n i
      rw [hb, hm]
      have hterm : ∀ j : Spin,
          (∑' o : Observation n,
            observationLaw lam hlam offspring n j o * censusState n o) =
          ENNReal.ofReal (m ^ n *
            (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))) :=
        fun j => ih j
      simp only [hterm]
      rw [tsum_fintype]
      have hchan : ∀ j : Spin, channel lam hlam i j =
          ENNReal.ofReal (channelWeight lam i j) := by
        intro j
        simp only [channel, PMF.ofFintype_apply]
      simp only [hchan]
      have hmul : ∀ j : Spin,
          ENNReal.ofReal (channelWeight lam i j) *
            ENNReal.ofReal (m ^ n *
              (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))) =
          ENNReal.ofReal (channelWeight lam i j * (m ^ n *
              (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)))) := by
        intro j
        rw [ENNReal.ofReal_mul (channelWeight_nonneg hlam i j)]
      simp only [hmul]
      rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun j _ =>
        mul_nonneg (channelWeight_nonneg hlam i j)
          (mul_nonneg (pow_nonneg hm0 n) (one_third_add_pow_mul_centred_nonneg hlam n j)))]
      have hsum : (∑ j : Spin, channelWeight lam i j * (m ^ n *
            (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))))
          = m ^ n * (1 / 3 +
              lam ^ (n + 1) * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
        have h1 : ∀ j : Spin, channelWeight lam i j * (m ^ n *
              (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)))
            = m ^ n * (channelWeight lam i j *
              (1 / 3 + lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))) := by
          intro j; ring
        simp only [h1]
        rw [← Finset.mul_sum, channelWeight_sum_affine]
      rw [hsum]
      rw [← ENNReal.ofReal_mul hm0]
      congr 1
      ring
theorem totalCensus_moment (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hm0 : 0 ≤ m) :
    ∀ (n : ℕ) (i : Spin),
      (∑' o : Observation n,
        observationLaw lam hlam offspring n i o * totalCensus n o) =
        ENNReal.ofReal (m ^ n) := by
  intro n
  induction n with
  | zero =>
      intro i
      change (∑' o : Spin, PMF.pure i o * (1 : ℝ≥0∞)) = ENNReal.ofReal (m ^ 0)
      rw [TheoremOS.Probability.tsum_pure_mul i (fun _ : Spin => (1 : ℝ≥0∞))]
      simp
  | succ n ih =>
      intro i
      have hb := (isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census
        (fun n : ℕ => totalCensus n) (fun n s => totalCensus_succ n s) n i
      rw [hb, hm]
      have hstep : (∑' j : Spin, channel lam hlam i j *
          (∑' o : Observation n,
            observationLaw lam hlam offspring n j o * totalCensus n o)) =
          ENNReal.ofReal (m ^ n) := by
        simp_rw [ih]
        rw [ENNReal.tsum_mul_right, (channel lam hlam i).tsum_coe]
        simp
      rw [hstep]
      rw [← ENNReal.ofReal_mul hm0]
      congr 1
      rw [pow_succ']

lemma tsum_pure_toReal_mul {α : Type*} (i : α) (F : α → ℝ) :
    ∑' o, ((PMF.pure i : PMF α) o).toReal * F o = F i := by
  rw [tsum_eq_single i]
  · simp
  · intro b hb; simp [PMF.pure_apply, hb]
lemma mul_mem_I {a b : ℝ} (ha1 : -(1/2:ℝ) ≤ a) (ha2 : a ≤ 1)
    (hb1 : -(1/2:ℝ) ≤ b) (hb2 : b ≤ 1) : -(1/2:ℝ) ≤ a*b ∧ a*b ≤ 1 := by
  constructor
  · rcases le_total 0 b with hb | hb <;> nlinarith
  · rcases le_total 0 b with hb | hb <;> nlinarith
lemma pow_bounds {lam : ℝ} (hlam : Admissible lam) (n : ℕ) :
    -(1/2 : ℝ) ≤ lam ^ n ∧ lam ^ n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have h := mul_mem_I ih.1 ih.2 hlam.1 hlam.2
    rw [pow_succ]; exact h
lemma phi_nonneg {lam : ℝ} (hlam : Admissible lam) (n : ℕ) (i : Spin) :
    0 ≤ (1/3 : ℝ) + lam^n * ((if i = (0:Spin) then (1:ℝ) else 0) - 1/3) := by
  obtain ⟨h1, h2⟩ := pow_bounds hlam n
  split_ifs with h <;> nlinarith
lemma channelWeight_shift (lam : ℝ) (i : Spin) (c : ℝ) :
    ∑ j : Spin, channelWeight lam i j *
        ((1:ℝ)/3 + c * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3))
      = (1:ℝ)/3 + c * (lam * ((if i = (0:Spin) then (1:ℝ) else 0) - 1/3)) := by
  have h1 : ∀ j : Spin, channelWeight lam i j * ((1:ℝ)/3 + c * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3))
      = channelWeight lam i j * (1/3) + c * (channelWeight lam i j * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)) := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum]
  have h2 : ∑ j : Spin, channelWeight lam i j * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)
      = lam * ((if i = (0:Spin) then (1:ℝ) else 0) - 1/3) := channelWeight_centred_eigen lam i
  rw [channelWeight_sum, h2]
  ring
lemma channel_apply {lam : ℝ} (hlam : Admissible lam) (i j : Spin) :
    channel lam hlam i j = ENNReal.ofReal (channelWeight lam i j) := by
  rw [channel, PMF.ofFintype_apply]
lemma channel_tsum_mul_const (lam : ℝ) (hlam : Admissible lam) (i : Spin) (c : ℝ≥0∞) :
    ∑' j : Spin, channel lam hlam i j * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
lemma tsum_ne_top_fin {α : Type*} [Fintype α] (f : α → ℝ≥0∞) (h : ∀ a, f a ≠ ∞) :
    ∑' a, f a ≠ ∞ := by
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.2 (fun a _ => h a)
lemma step_A_tsum {lam : ℝ} (hlam : Admissible lam) (i : Spin) (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ∑' j : Spin, channel lam hlam i j *
        ENNReal.ofReal (a * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)))
      = ENNReal.ofReal (a * ((1:ℝ)/3 + lam^(n+1) * ((if i = (0:Spin) then (1:ℝ) else 0) - 1/3))) := by
  have hw : ∀ j : Spin, channel lam hlam i j *
        ENNReal.ofReal (a * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)))
      = ENNReal.ofReal (channelWeight lam i j * (a * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)))) := by
    intro j
    rw [channel_apply hlam, ← ENNReal.ofReal_mul (channelWeight_nonneg hlam i j)]
  rw [tsum_congr hw, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun j : Spin => channelWeight lam i j * (a * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3))))
      (fun j _ => mul_nonneg (channelWeight_nonneg hlam i j) (mul_nonneg ha (phi_nonneg hlam n j)))]
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => by ring :
      ∀ j ∈ (Finset.univ : Finset Spin),
        channelWeight lam i j * (a * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3)))
          = a * (channelWeight lam i j * ((1:ℝ)/3 + lam^n * ((if j = (0:Spin) then (1:ℝ) else 0) - 1/3))))]
  rw [← Finset.mul_sum, channelWeight_shift, pow_succ]
  ring
lemma second_moment_finite (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (n : ℕ) (i : Spin)
    (X Y : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n+1) s = (s.map (X n)).sum)
    (hY : ∀ (n : ℕ) (s : Multiset (Observation n)), Y (n+1) s = (s.map (Y n)).sum)
    (hXY : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * Y n o) ≠ ∞)
    (hX1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o ≠ ∞)
    (hY1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * Y n o ≠ ∞) :
    ∑' o : Observation (n+1), observationLaw lam hlam offspring (n+1) i o * (X (n+1) o * Y (n+1) o) ≠ ∞ := by
  rw [(isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census_mul_census X Y hX hY n i, hm, hβ]
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact tsum_ne_top_fin _
      (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hXY j))
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ?_ ?_)
    · exact tsum_ne_top_fin _
        (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hX1 j))
    · exact tsum_ne_top_fin _
        (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hY1 j))
theorem signedCensus_moment_data (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (hm0 : 0 ≤ m) (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1) :
    ∀ (n : ℕ) (i : Spin),
      (∑' o : Observation n, observationLaw lam hlam offspring n i o * M n o
        = ENNReal.ofReal (m ^ n)) ∧
      (∑' o : Observation n, observationLaw lam hlam offspring n i o * X n o
        = ENNReal.ofReal (m ^ n * ((1:ℝ)/3 + lam ^ n * ((if i = (0 : Spin) then (1:ℝ) else 0) - 1 / 3)))) ∧
      (∑' o : Observation n, (observationLaw lam hlam offspring n i o).toReal *
          ((X n o).toReal - (M n o).toReal / 3)
        = (m * lam) ^ n * ((if i = (0 : Spin) then (1:ℝ) else 0) - 1 / 3)) ∧
      (∑' o : Observation n, observationLaw lam hlam offspring n i o * (X n o * X n o) ≠ ∞) ∧
      (∑' o : Observation n, observationLaw lam hlam offspring n i o * (X n o * M n o) ≠ ∞) ∧
      (∑' o : Observation n, observationLaw lam hlam offspring n i o * (M n o * M n o) ≠ ∞) := by
  intro n
  induction n with
  | zero =>
    intro i
    have hp : observationLaw lam hlam offspring 0 i =
        (PMF.pure (show Observation 0 from i) : PMF (Observation 0)) := rfl
    have hXne : X 0 i ≠ ∞ := by
      rw [hX0 i]
      split_ifs with h
      · exact ENNReal.one_ne_top
      · exact ENNReal.zero_ne_top
    have hMne : M 0 i ≠ ∞ := by
      rw [hM0 i]; exact ENNReal.one_ne_top
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp, TheoremOS.Probability.tsum_pure_mul, hM0 i, pow_zero, ENNReal.ofReal_one]
    · rw [hp, TheoremOS.Probability.tsum_pure_mul, hX0 i, pow_zero]
      simp only [one_mul]
      split_ifs <;> simp
    · rw [hp, tsum_pure_toReal_mul, hM0 i, hX0 i, pow_zero, one_mul]
      rw [ENNReal.toReal_one]
      split_ifs <;> simp
    · rw [hp, TheoremOS.Probability.tsum_pure_mul]; exact ENNReal.mul_ne_top hXne hXne
    · rw [hp, TheoremOS.Probability.tsum_pure_mul]; exact ENNReal.mul_ne_top hXne hMne
    · rw [hp, TheoremOS.Probability.tsum_pure_mul]; exact ENNReal.mul_ne_top hMne hMne
  | succ n ih =>
    intro i
    have hinnerM : ∀ j : Spin,
        (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o)
          = ENNReal.ofReal (m ^ n) := fun j => (ih j).1
    have hinnerX : ∀ j : Spin,
        (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o)
          = ENNReal.ofReal (m ^ n * ((1:ℝ)/3 + lam ^ n * ((if j = (0 : Spin) then (1:ℝ) else 0) - 1 / 3))) :=
      fun j => (ih j).2.1
    have h1 : ∑' o : Observation (n + 1), observationLaw lam hlam offspring (n + 1) i o * M (n + 1) o
        = ENNReal.ofReal (m ^ (n + 1)) := by
      rw [(isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census M hM n i, hm]
      simp only [hinnerM]
      rw [channel_tsum_mul_const, ← ENNReal.ofReal_mul hm0, pow_succ']
    have h2 : ∑' o : Observation (n + 1), observationLaw lam hlam offspring (n + 1) i o * X (n + 1) o
        = ENNReal.ofReal (m ^ (n + 1) * ((1:ℝ)/3 + lam ^ (n + 1) * ((if i = (0 : Spin) then (1:ℝ) else 0) - 1 / 3))) := by
      rw [(isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census X hX n i, hm]
      simp only [hinnerX]
      rw [step_A_tsum hlam i (m ^ n) (pow_nonneg hm0 n) n]
      rw [← ENNReal.ofReal_mul hm0]
      congr 1
      rw [pow_succ']
      ring
    have hfinM : ∑' o : Observation (n + 1), observationLaw lam hlam offspring (n + 1) i o * M (n + 1) o ≠ ∞ := by
      rw [h1]; exact ENNReal.ofReal_ne_top
    have hfinX : ∑' o : Observation (n + 1), observationLaw lam hlam offspring (n + 1) i o * X (n + 1) o ≠ ∞ := by
      rw [h2]; exact ENNReal.ofReal_ne_top
    have hsumM := TheoremOS.Probability.summable_toReal_mul_toReal
      (observationLaw lam hlam offspring (n + 1) i) (M (n + 1)) hfinM
    have hsumX := TheoremOS.Probability.summable_toReal_mul_toReal
      (observationLaw lam hlam offspring (n + 1) i) (X (n + 1)) hfinX
    have h3 : ∑' o : Observation (n + 1), (observationLaw lam hlam offspring (n + 1) i o).toReal *
        ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3)
        = (m * lam) ^ (n + 1) * ((if i = (0 : Spin) then (1:ℝ) else 0) - 1 / 3) := by
      have hsplit : ∀ o : Observation (n + 1),
          (observationLaw lam hlam offspring (n + 1) i o).toReal *
            ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3)
          = (observationLaw lam hlam offspring (n + 1) i o).toReal * (X (n + 1) o).toReal
            - (1/3) * ((observationLaw lam hlam offspring (n + 1) i o).toReal * (M (n + 1) o).toReal) := by
        intro o; ring
      rw [tsum_congr hsplit, hsumX.tsum_sub (hsumM.mul_left (1/3)), tsum_mul_left,
        TheoremOS.Probability.tsum_toReal_mul_toReal _ _ hfinX,
        TheoremOS.Probability.tsum_toReal_mul_toReal _ _ hfinM, h2, h1,
        ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hm0 (n+1)) (phi_nonneg hlam (n+1) i)),
        ENNReal.toReal_ofReal (pow_nonneg hm0 (n+1)), mul_pow]
      ring
    refine ⟨h1, h2, h3, ?_, ?_, ?_⟩
    · exact second_moment_finite lam hlam offspring m β hm hβ n i X X hX hX
        (fun j => (ih j).2.2.2.1)
        (fun j => by rw [hinnerX j]; exact ENNReal.ofReal_ne_top)
        (fun j => by rw [hinnerX j]; exact ENNReal.ofReal_ne_top)
    · exact second_moment_finite lam hlam offspring m β hm hβ n i X M hX hM
        (fun j => (ih j).2.2.2.2.1)
        (fun j => by rw [hinnerX j]; exact ENNReal.ofReal_ne_top)
        (fun j => by rw [hinnerM j]; exact ENNReal.ofReal_ne_top)
    · exact second_moment_finite lam hlam offspring m β hm hβ n i M M hM hM
        (fun j => (ih j).2.2.2.2.2)
        (fun j => by rw [hinnerM j]; exact ENNReal.ofReal_ne_top)
        (fun j => by rw [hinnerM j]; exact ENNReal.ofReal_ne_top)
lemma tsum_sq_sub_div_three {α : Type*} (p : α → ℝ≥0∞) (X M : α → ℝ≥0∞)
    (hXX : ∑' a, p a * (X a * X a) ≠ ∞)
    (hXM : ∑' a, p a * (X a * M a) ≠ ∞)
    (hMM : ∑' a, p a * (M a * M a) ≠ ∞) :
    ∑' a, (p a).toReal * ((X a).toReal - (M a).toReal / 3) ^ 2 =
      (∑' a, p a * (X a * X a)).toReal - (2 / 3) * (∑' a, p a * (X a * M a)).toReal
        + (1 / 9) * (∑' a, p a * (M a * M a)).toReal := by
  have hXXs : Summable fun a => (p a).toReal * (X a).toReal * (X a).toReal :=
    (ENNReal.summable_toReal hXX).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  have hXMs : Summable fun a => (p a).toReal * (X a).toReal * (M a).toReal :=
    (ENNReal.summable_toReal hXM).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  have hMMs : Summable fun a => (p a).toReal * (M a).toReal * (M a).toReal :=
    (ENNReal.summable_toReal hMM).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  have hpt : ∀ a, (p a).toReal * ((X a).toReal - (M a).toReal / 3) ^ 2 =
      ((p a).toReal * (X a).toReal * (X a).toReal
        - ((2 / 3) * ((p a).toReal * (X a).toReal * (M a).toReal)
          - (1 / 9) * ((p a).toReal * (M a).toReal * (M a).toReal))) := by
    intro a; ring
  have hsplit := hXXs.tsum_sub ((hXMs.mul_left (2/3)).sub (hMMs.mul_left (1/9)))
  have hinner := (hXMs.mul_left (2/3)).tsum_sub (hMMs.mul_left (1/9))
  rw [tsum_congr hpt, hsplit, hinner, tsum_mul_left, tsum_mul_left]
  have kXX : (∑' a, p a * (X a * X a)).toReal =
      ∑' a, (p a).toReal * (X a).toReal * (X a).toReal := by
    rw [ENNReal.tsum_toReal_eq fun a => ENNReal.ne_top_of_tsum_ne_top hXX a]
    exact tsum_congr fun a => by rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring
  have kXM : (∑' a, p a * (X a * M a)).toReal =
      ∑' a, (p a).toReal * (X a).toReal * (M a).toReal := by
    rw [ENNReal.tsum_toReal_eq fun a => ENNReal.ne_top_of_tsum_ne_top hXM a]
    exact tsum_congr fun a => by rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring
  have kMM : (∑' a, p a * (M a * M a)).toReal =
      ∑' a, (p a).toReal * (M a).toReal * (M a).toReal := by
    rw [ENNReal.tsum_toReal_eq fun a => ENNReal.ne_top_of_tsum_ne_top hMM a]
    exact tsum_congr fun a => by rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring
  rw [kXX, kXM, kMM]
  simp only [mul_assoc]
  ring
lemma summable_centred_sq {α : Type*} (p : α → ℝ≥0∞) (X M : α → ℝ≥0∞)
    (hXX : ∑' a, p a * (X a * X a) ≠ ∞)
    (hXM : ∑' a, p a * (X a * M a) ≠ ∞)
    (hMM : ∑' a, p a * (M a * M a) ≠ ∞) :
    Summable fun a => (p a).toReal * ((X a).toReal - (M a).toReal / 3) ^ 2 := by
  have hA : Summable fun a => (p a).toReal * (X a).toReal * (X a).toReal :=
    (ENNReal.summable_toReal hXX).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  have hB : Summable fun a => (p a).toReal * (X a).toReal * (M a).toReal :=
    (ENNReal.summable_toReal hXM).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  have hC : Summable fun a => (p a).toReal * (M a).toReal * (M a).toReal :=
    (ENNReal.summable_toReal hMM).congr (fun a => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
  exact ((hA.sub (hB.mul_left (2/3))).add (hC.mul_left (1/9))).congr (fun a => by ring)
lemma sum_mul_toReal_fin {ι : Type*} [Fintype ι] (K S : ι → ℝ≥0∞)
    (hK : ∀ j, K j ≠ ∞) (hS : ∀ j, S j ≠ ∞) :
    (∑ j, K j * S j).toReal = ∑ j, (K j).toReal * (S j).toReal := by
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.mul_ne_top (hK j) (hS j))]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_mul
lemma spin_tsum_channel_toReal (lam : ℝ) (hlam : Admissible lam) (i : Spin)
    (F : Spin → ℝ≥0∞) (hF : ∀ j, F j ≠ ∞) :
    (∑' j : Spin, channel lam hlam i j * F j).toReal
      = ∑ j : Spin, channelWeight lam i j * (F j).toReal := by
  rw [tsum_fintype, sum_mul_toReal_fin (fun j : Spin => channel lam hlam i j) F
      (fun j => PMF.apply_ne_top (channel lam hlam i) j) hF]
  exact Finset.sum_congr rfl fun j _ => by
    rw [channel_apply hlam, ENNReal.toReal_ofReal (channelWeight_nonneg hlam i j)]
lemma census_pair_toReal (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) (m β : ℝ)
    (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (hm0 : 0 ≤ m) (hβ0 : 0 ≤ β)
    (X Y : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hY : ∀ (n : ℕ) (s : Multiset (Observation n)), Y (n + 1) s = (s.map (Y n)).sum)
    (n : ℕ) (i : Spin)
    (hXY : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * Y n o) ≠ ∞)
    (hX1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o ≠ ∞)
    (hY1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * Y n o ≠ ∞) :
    (∑' o : Observation (n + 1),
        observationLaw lam hlam offspring (n + 1) i o * (X (n + 1) o * Y (n + 1) o)).toReal
      = m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * Y n o)).toReal)
        + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal) *
               (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * Y n o).toReal)) := by
  rw [(isBroadcastLaw_observationLaw lam hlam offspring).tsum_mul_census_mul_census X Y hX hY n i, hm, hβ]
  have hSA : (∑' j : Spin, channel lam hlam i j *
      ∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * Y n o)) ≠ ∞ :=
    tsum_ne_top_fin _ (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hXY j))
  have hSX : (∑' j : Spin, channel lam hlam i j *
      ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o) ≠ ∞ :=
    tsum_ne_top_fin _ (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hX1 j))
  have hSY : (∑' j : Spin, channel lam hlam i j *
      ∑' o : Observation n, observationLaw lam hlam offspring n j o * Y n o) ≠ ∞ :=
    tsum_ne_top_fin _ (fun j => ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (hY1 j))
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSA)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hSX hSY))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hm0, ENNReal.toReal_ofReal hβ0]
  have hprod : (∑' j : Spin, channel lam hlam i j *
        ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o) *
        (∑' j : Spin, channel lam hlam i j *
        ∑' o : Observation n, observationLaw lam hlam offspring n j o * Y n o) ≠ ∞ :=
    ENNReal.mul_ne_top hSX hSY
  rw [ENNReal.toReal_mul]
  rw [spin_tsum_channel_toReal lam hlam i _ hXY,
    spin_tsum_channel_toReal lam hlam i _ hX1,
    spin_tsum_channel_toReal lam hlam i _ hY1]
lemma toReal_first_X {lam : ℝ} (hlam : Admissible lam) (offspring : PMF ℕ) {m : ℝ} (hm0 : 0 ≤ m)
    (X : (n : ℕ) → Observation n → ℝ≥0∞) (n : ℕ) (j : Spin)
    (h : ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o
        = ENNReal.ofReal (m ^ n * ((1:ℝ)/3 + lam ^ n * ((if j = (0 : Spin) then (1:ℝ) else 0) - 1 / 3)))) :
    (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal
      = m ^ n * ((1:ℝ)/3 + lam ^ n * ((if j = (0 : Spin) then (1:ℝ) else 0) - 1 / 3)) := by
  rw [h, ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg hm0 n) (phi_nonneg hlam n j))]
lemma sum_mul_centre {ι : Type*} [Fintype ι] (K A B C : ι → ℝ) :
    ∑ j, K j * (A j - (2/3) * B j + (1/9) * C j)
      = (∑ j, K j * A j) - (2/3) * (∑ j, K j * B j) + (1/9) * (∑ j, K j * C j) := by
  have hpt : ∀ j, K j * (A j - (2/3) * B j + (1/9) * C j)
      = (K j * A j - (2/3) * (K j * B j)) + (1/9) * (K j * C j) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
theorem signedCensus_second_moment_succ (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (hm0 : 0 ≤ m) (hβ0 : 0 ≤ β)
    (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1)
    (n : ℕ) (i : Spin) :
    (∑' o : Observation (n + 1),
        (observationLaw lam hlam offspring (n + 1) i o).toReal *
          ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3) ^ 2)
      = m * ∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n,
          (observationLaw lam hlam offspring n j o).toReal * ((X n o).toReal - (M n o).toReal / 3) ^ 2)
        + β * lam ^ 2 * (m * lam) ^ (2 * n) *
            ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := by
  have H := signedCensus_moment_data lam hlam offspring m β hm hβ hm0 X M hX hM hX0 hM0
  -- first moments at level n
  have hX1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o ≠ ∞ :=
    fun j => by rw [(H n j).2.1]; exact ENNReal.ofReal_ne_top
  have hM1 : ∀ j : Spin, ∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o ≠ ∞ :=
    fun j => by rw [(H n j).1]; exact ENNReal.ofReal_ne_top
  -- real values of the level-n first moments
  have haX : ∀ j : Spin,
      (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal
        = m ^ n * ((1:ℝ)/3 + lam ^ n * ((if j = (0 : Spin) then (1:ℝ) else 0) - 1 / 3)) :=
    fun j => toReal_first_X hlam offspring hm0 X n j (H n j).2.1
  have haM : ∀ j : Spin,
      (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal = m ^ n :=
    fun j => by rw [(H n j).1, ENNReal.toReal_ofReal (pow_nonneg hm0 n)]
  -- pointwise expansion of Q at level n
  have hQn : ∀ j : Spin,
      (∑' o : Observation n,
          (observationLaw lam hlam offspring n j o).toReal *
            ((X n o).toReal - (M n o).toReal / 3) ^ 2)
        = (∑' o : Observation n,
            observationLaw lam hlam offspring n j o * (X n o * X n o)).toReal
          - (2/3) * (∑' o : Observation n,
            observationLaw lam hlam offspring n j o * (X n o * M n o)).toReal
          + (1/9) * (∑' o : Observation n,
            observationLaw lam hlam offspring n j o * (M n o * M n o)).toReal :=
    fun j => tsum_sq_sub_div_three (observationLaw lam hlam offspring n j) (X n) (M n)
      (H n j).2.2.2.1 (H n j).2.2.2.2.1 (H n j).2.2.2.2.2
  -- pair-moment recursions at level n
  have hpairXX := census_pair_toReal lam hlam offspring m β hm hβ hm0 hβ0 X X hX hX n i
    (fun j => (H n j).2.2.2.1) hX1 hX1
  have hpairXM := census_pair_toReal lam hlam offspring m β hm hβ hm0 hβ0 X M hX hM n i
    (fun j => (H n j).2.2.2.2.1) hX1 hM1
  have hpairMM := census_pair_toReal lam hlam offspring m β hm hβ hm0 hβ0 M M hM hM n i
    (fun j => (H n j).2.2.2.2.2) hM1 hM1
  -- weighted mean identity
  have hmean :
      (∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal)
        - (1/3) * (∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)
      = (m * lam) ^ n * (lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
    have hpt : ∀ j : Spin,
        (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal
          - (1/3) * (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal
        = m ^ n * lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) := by
      intro j; rw [haX j, haM j]; ring
    have h1 :
        (∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal)
          - (1/3) * (∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)
        = ∑ j : Spin, channelWeight lam i j *
          ((∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal
            - (1/3) * (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1]
    calc ∑ j : Spin, channelWeight lam i j *
          ((∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal
            - (1/3) * (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)
        = ∑ j : Spin, channelWeight lam i j *
            (m ^ n * lam ^ n * ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) :=
          Finset.sum_congr rfl (fun j _ => by rw [hpt j])
      _ = m ^ n * lam ^ n * ∑ j : Spin, channelWeight lam i j *
            ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = m ^ n * lam ^ n * (lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
          rw [channelWeight_centred_eigen]
      _ = (m * lam) ^ n * (lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3)) := by
          rw [mul_pow]
  have hpow : (m * lam) ^ (2 * n) = ((m * lam) ^ n) ^ 2 := by
    rw [show 2 * n = n + n by ring, pow_add, pow_two]
  calc (∑' o : Observation (n + 1),
        (observationLaw lam hlam offspring (n + 1) i o).toReal *
          ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3) ^ 2)
      = (∑' o : Observation (n + 1),
          observationLaw lam hlam offspring (n + 1) i o * (X (n + 1) o * X (n + 1) o)).toReal
        - (2/3) * (∑' o : Observation (n + 1),
          observationLaw lam hlam offspring (n + 1) i o * (X (n + 1) o * M (n + 1) o)).toReal
        + (1/9) * (∑' o : Observation (n + 1),
          observationLaw lam hlam offspring (n + 1) i o * (M (n + 1) o * M (n + 1) o)).toReal :=
        tsum_sq_sub_div_three (observationLaw lam hlam offspring (n+1) i) (X (n+1)) (M (n+1))
          (H (n+1) i).2.2.2.1 (H (n+1) i).2.2.2.2.1 (H (n+1) i).2.2.2.2.2
    _ = m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * X n o)).toReal)
          + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal) *
            (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal))
        - (2/3) * (m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * M n o)).toReal)
          + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal) *
            (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)))
        + (1/9) * (m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, observationLaw lam hlam offspring n j o * (M n o * M n o)).toReal)
          + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal) *
            (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal))) := by
        rw [hpairXX, hpairXM, hpairMM]
    _ = m * ∑ j : Spin, channelWeight lam i j *
          ((∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * X n o)).toReal
            - (2/3) * (∑' o : Observation n, observationLaw lam hlam offspring n j o * (X n o * M n o)).toReal
            + (1/9) * (∑' o : Observation n, observationLaw lam hlam offspring n j o * (M n o * M n o)).toReal)
        + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal)
            - (1/3) * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)) ^ 2 := by
        rw [sum_mul_centre]
        ring
    _ = m * ∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n,
          (observationLaw lam hlam offspring n j o).toReal * ((X n o).toReal - (M n o).toReal / 3) ^ 2)
        + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal)
            - (1/3) * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)) ^ 2 := by
        exact congrArg (fun z => m * z + β * ((∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * X n o).toReal)
            - (1/3) * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, observationLaw lam hlam offspring n j o * M n o).toReal)) ^ 2)
          (Finset.sum_congr rfl (fun j _ => by rw [← hQn j]))
    _ = m * ∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n,
          (observationLaw lam hlam offspring n j o).toReal * ((X n o).toReal - (M n o).toReal / 3) ^ 2)
        + β * ((m * lam) ^ n * (lam * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3))) ^ 2 := by
        rw [hmean]
    _ = m * ∑ j : Spin, channelWeight lam i j *
          (∑' o : Observation n,
          (observationLaw lam hlam offspring n j o).toReal * ((X n o).toReal - (M n o).toReal / 3) ^ 2)
        + β * lam ^ 2 * (m * lam) ^ (2 * n) *
            ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := by
        rw [hpow]; ring
theorem signedCensus_second_moment_le (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (C : ℝ) (hm1 : 1 < m) (hβ0 : 0 ≤ β) (hC0 : 4 / 9 ≤ C)
    (hC : 4 / 9 * (β * lam ^ 2) ≤ C * (m * (m * lam ^ 2 - 1)))
    (hKS : 1 < m * lam ^ 2)
    (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1)
    (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ∧
    (∑' o : Observation n, (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ≤ C * (m * lam) ^ (2 * n) := by
  have hm0 : 0 ≤ m := le_of_lt (lt_trans zero_lt_one hm1)
  -- square bound for the centred root symbol
  have phi_sq : ∀ j : Spin, ((if j = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 ≤ 4 / 9 := by
    intro j; fin_cases j <;> norm_num
  have H := signedCensus_moment_data lam hlam offspring m β hm hβ hm0 X M hX hM hX0 hM0
  have hsumm : ∀ n i, Summable (fun o : Observation n =>
      (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) := by
    intro n i
    have hYY := (H n i).2.2.2.1
    have hYM := (H n i).2.2.2.2.1
    have hMM := (H n i).2.2.2.2.2
    have hA : Summable fun a : Observation n =>
        (observationLaw lam hlam offspring n i a).toReal * (X n a).toReal * (X n a).toReal :=
      (ENNReal.summable_toReal hYY).congr (fun a => by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
    have hB : Summable fun a : Observation n =>
        (observationLaw lam hlam offspring n i a).toReal * (X n a).toReal * (M n a).toReal :=
      (ENNReal.summable_toReal hYM).congr (fun a => by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
    have hD : Summable fun a : Observation n =>
        (observationLaw lam hlam offspring n i a).toReal * (M n a).toReal * (M n a).toReal :=
      (ENNReal.summable_toReal hMM).congr (fun a => by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]; ring)
    exact ((hA.sub (hB.mul_left (2 / 3))).add (hD.mul_left (1 / 9))).congr (fun a => by ring)
  refine ⟨hsumm n i, ?_⟩
  have key : ∀ n : ℕ, ∀ i : Spin,
      (∑' o : Observation n, (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ≤ C * (m * lam) ^ (2 * n) := by
    intro n
    induction n with
    | zero =>
      intro i
      have hp : observationLaw lam hlam offspring 0 i =
          (PMF.pure (show Observation 0 from i) : PMF (Observation 0)) := rfl
      have h : (∑' o : Observation 0, (observationLaw lam hlam offspring 0 i o).toReal *
          ((X 0 o).toReal - (M 0 o).toReal / 3) ^ 2)
          = ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := by
        rw [hp, tsum_pure_toReal_mul, hX0 i, hM0 i]
        split_ifs <;> norm_num
      rw [h, pow_zero, mul_one]
      exact (phi_sq i).trans hC0
    | succ n ih =>
      intro i
      have hphi := phi_sq i
      have hlam2 : (0 : ℝ) ≤ lam ^ 2 := sq_nonneg lam
      have hpow : (0 : ℝ) ≤ (m * lam) ^ (2 * n) := by
        rw [pow_mul]; exact pow_nonneg (sq_nonneg _) n
      have hw : ∀ j : Spin, 0 ≤ channelWeight lam i j := fun j => channelWeight_nonneg hlam i j
      have hstep := signedCensus_second_moment_succ lam hlam offspring m β hm hβ hm0 hβ0
        X M hX hM hX0 hM0 n i
      have havg : (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
              ((X n o).toReal - (M n o).toReal / 3) ^ 2))
          ≤ ∑ j : Spin, channelWeight lam i j * (C * (m * lam) ^ (2 * n)) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih j) (hw j)
      have hsum_const : (∑ j : Spin, channelWeight lam i j * (C * (m * lam) ^ (2 * n)))
          = C * (m * lam) ^ (2 * n) := by
        rw [← Finset.sum_mul, channelWeight_sum, one_mul]
      have hmul : m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
              ((X n o).toReal - (M n o).toReal / 3) ^ 2))
          ≤ m * (C * (m * lam) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (havg.trans_eq hsum_const) hm0
      have hnoise : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
          ≤ 4 / 9 * (β * lam ^ 2) := by
        have hle := mul_le_mul_of_nonneg_left hphi (mul_nonneg hβ0 hlam2)
        linarith
      have hkey : m * C + β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
          ≤ C * (m * lam) ^ 2 := by
        have h1 : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
            ≤ C * (m * (m * lam ^ 2 - 1)) := hnoise.trans hC
        have h2 : m * C + C * (m * (m * lam ^ 2 - 1)) = C * (m * lam) ^ 2 := by ring
        linarith
      calc (∑' o : Observation (n + 1), (observationLaw lam hlam offspring (n + 1) i o).toReal *
            ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3) ^ 2)
          = m * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
                ((X n o).toReal - (M n o).toReal / 3) ^ 2))
            + β * lam ^ 2 * (m * lam) ^ (2 * n) *
              ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := hstep
        _ = m * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
                ((X n o).toReal - (M n o).toReal / 3) ^ 2))
            + (β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by ring
        _ ≤ m * (C * (m * lam) ^ (2 * n))
            + (β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by
            have := mul_le_mul_of_nonneg_right hnoise hpow
            linarith [hmul]
        _ = (m * C + β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by ring
        _ ≤ (C * (m * lam) ^ 2) * (m * lam) ^ (2 * n) :=
            mul_le_mul_of_nonneg_right hkey hpow
        _ = C * (m * lam) ^ (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]; ring
  exact key n i
lemma phi_sq_le_d2 (i : Spin) :
    ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 ≤ 4 / 9 := by
  fin_cases i <;> norm_num
theorem signedCensus_second_moment_le_d2 (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (C : ℝ) (hm1 : 1 < m) (hβ0 : 0 ≤ β) (hC0 : 4 / 9 ≤ C)
    (hC : 4 / 9 * (β * lam ^ 2) ≤ C * (m * (m * lam ^ 2 - 1)))
    (hKS : 1 < m * lam ^ 2)
    (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1)
    (n : ℕ) (i : Spin) :
    Summable (fun o : Observation n =>
      (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ∧
    (∑' o : Observation n, (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ≤ C * (m * lam) ^ (2 * n) := by
  have hm0 : 0 ≤ m := le_of_lt (lt_trans zero_lt_one hm1)
  have hmpos : 0 < m := lt_trans zero_lt_one hm1
  have H := signedCensus_moment_data lam hlam offspring m β hm hβ hm0 X M hX hM hX0 hM0
  have hsumm : ∀ n i, Summable (fun o : Observation n =>
      (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) := fun n i =>
    summable_centred_sq _ _ _ (H n i).2.2.2.1 (H n i).2.2.2.2.1 (H n i).2.2.2.2.2
  refine ⟨hsumm n i, ?_⟩
  -- uniform-in-index bound at every level
  have key : ∀ n : ℕ, ∀ i : Spin,
      (∑' o : Observation n, (observationLaw lam hlam offspring n i o).toReal *
        ((X n o).toReal - (M n o).toReal / 3) ^ 2) ≤ C * (m * lam) ^ (2 * n) := by
    intro n
    induction n with
    | zero =>
      intro i
      have hp : observationLaw lam hlam offspring 0 i =
          (PMF.pure (show Observation 0 from i) : PMF (Observation 0)) := rfl
      have h : (∑' o : Observation 0, (observationLaw lam hlam offspring 0 i o).toReal *
          ((X 0 o).toReal - (M 0 o).toReal / 3) ^ 2)
          = ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := by
        rw [hp, tsum_pure_toReal_mul, hX0 i, hM0 i]
        split_ifs <;> norm_num
      rw [h, pow_zero, mul_one]
      exact (phi_sq_le_d2 i).trans hC0
    | succ n ih =>
      intro i
      have hphi := phi_sq_le_d2 i
      have hlam2 : (0:ℝ) ≤ lam ^ 2 := sq_nonneg lam
      have hpow : (0:ℝ) ≤ (m * lam) ^ (2 * n) := by
        rw [pow_mul]; exact pow_nonneg (sq_nonneg _) n
      have hw : ∀ j : Spin, 0 ≤ channelWeight lam i j := fun j => channelWeight_nonneg hlam i j
      have hstep := signedCensus_second_moment_succ lam hlam offspring m β hm hβ hm0 hβ0
        X M hX hM hX0 hM0 n i
      have havg : (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
              ((X n o).toReal - (M n o).toReal / 3) ^ 2))
          ≤ ∑ j : Spin, channelWeight lam i j * (C * (m * lam) ^ (2 * n)) := by
        exact Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (ih j) (hw j)
      have hsum_const : (∑ j : Spin, channelWeight lam i j * (C * (m * lam) ^ (2 * n)))
          = C * (m * lam) ^ (2 * n) := by
        rw [← Finset.sum_mul, channelWeight_sum, one_mul]
      have hmul : m * (∑ j : Spin, channelWeight lam i j *
            (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
              ((X n o).toReal - (M n o).toReal / 3) ^ 2))
          ≤ m * (C * (m * lam) ^ (2 * n)) :=
        mul_le_mul_of_nonneg_left (havg.trans_eq hsum_const) hm0
      have hfs : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 ≤ 4 / 9 * (β * lam ^ 2) := by
        have hb2 : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
            ≤ β * lam ^ 2 * (4/9) := mul_le_mul_of_nonneg_left hphi (mul_nonneg hβ0 hlam2)
        linarith
      have hkey : m * C + β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
          ≤ C * (m * lam) ^ 2 := by
        have hb2' : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
            ≤ 4 / 9 * (β * lam ^ 2) := by
          have hle := mul_le_mul_of_nonneg_left hphi (mul_nonneg hβ0 hlam2)
          linarith
        have h1 : β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2
            ≤ C * (m * (m * lam ^ 2 - 1)) := hb2'.trans hC
        have h2 : m * C + C * (m * (m * lam ^ 2 - 1)) = C * (m * lam) ^ 2 := by ring
        linarith
      calc (∑' o : Observation (n + 1), (observationLaw lam hlam offspring (n + 1) i o).toReal *
            ((X (n + 1) o).toReal - (M (n + 1) o).toReal / 3) ^ 2)
          = m * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
                ((X n o).toReal - (M n o).toReal / 3) ^ 2))
            + β * lam ^ 2 * (m * lam) ^ (2 * n) *
              ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2 := hstep
        _ = m * (∑ j : Spin, channelWeight lam i j *
              (∑' o : Observation n, (observationLaw lam hlam offspring n j o).toReal *
                ((X n o).toReal - (M n o).toReal / 3) ^ 2))
            + (β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by ring
        _ ≤ m * (C * (m * lam) ^ (2 * n))
            + (β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by
            have := mul_le_mul_of_nonneg_right hfs hpow
            linarith [hmul]
        _ = (m * C + β * lam ^ 2 * ((if i = (0 : Spin) then (1 : ℝ) else 0) - 1 / 3) ^ 2) *
              (m * lam) ^ (2 * n) := by ring
        _ ≤ (C * (m * lam) ^ 2) * (m * lam) ^ (2 * n) :=
            mul_le_mul_of_nonneg_right hkey hpow
        _ = C * (m * lam) ^ (2 * (n + 1)) := by
            rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]; ring
  exact key n i
lemma pmfTV_observationLaw_lower (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (C : ℝ) (hm1 : 1 < m) (hβ0 : 0 ≤ β) (hC0 : 4 / 9 ≤ C)
    (hC : 4 / 9 * (β * lam ^ 2) ≤ C * (m * (m * lam ^ 2 - 1)))
    (hKS : 1 < m * lam ^ 2)
    (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1)
    (n : ℕ) :
    1 / (4 * C) ≤ TheoremOS.Probability.pmfTV
      (observationLaw lam hlam offspring n (0 : Spin))
      (observationLaw lam hlam offspring n (1 : Spin)) := by
  have hm0 : 0 ≤ m := le_of_lt (lt_trans zero_lt_one hm1)
  have hmpos : 0 < m := lt_trans zero_lt_one hm1
  let S : Observation n → ℝ := fun o => (X n o).toReal - (M n o).toReal / 3
  let Q0 : ℝ := ∑' o : Observation n,
    (observationLaw lam hlam offspring n (0 : Spin) o).toReal * S o ^ 2
  let Q1 : ℝ := ∑' o : Observation n,
    (observationLaw lam hlam offspring n (1 : Spin) o).toReal * S o ^ 2
  have H := signedCensus_moment_data lam hlam offspring m β hm hβ hm0 X M hX hM hX0 hM0
  have hsum0 : Summable fun o : Observation n =>
      (observationLaw lam hlam offspring n (0 : Spin) o).toReal * S o ^ 2 := by
    simpa only [S] using
      (signedCensus_second_moment_le_d2 lam hlam offspring m β hm hβ C hm1 hβ0 hC0 hC hKS
        X M hX hM hX0 hM0 n (0 : Spin)).1
  have hsum1 : Summable fun o : Observation n =>
      (observationLaw lam hlam offspring n (1 : Spin) o).toReal * S o ^ 2 := by
    simpa only [S] using
      (signedCensus_second_moment_le_d2 lam hlam offspring m β hm hβ C hm1 hβ0 hC0 hC hKS
        X M hX hM hX0 hM0 n (1 : Spin)).1
  have hQ0 : Q0 ≤ C * (m * lam) ^ (2 * n) := by
    simpa only [Q0, S] using
      (signedCensus_second_moment_le_d2 lam hlam offspring m β hm hβ C hm1 hβ0 hC0 hC hKS
        X M hX hM hX0 hM0 n (0 : Spin)).2
  have hQ1 : Q1 ≤ C * (m * lam) ^ (2 * n) := by
    simpa only [Q1, S] using
      (signedCensus_second_moment_le_d2 lam hlam offspring m β hm hβ C hm1 hβ0 hC0 hC hKS
        X M hX hM hX0 hM0 n (1 : Spin)).2
  have hmean0 := (H n (0 : Spin)).2.2.1
  have hmean1 := (H n (1 : Spin)).2.2.1
  have hgap : (∑' o : Observation n,
        (observationLaw lam hlam offspring n (0 : Spin) o).toReal * S o)
      - (∑' o : Observation n,
        (observationLaw lam hlam offspring n (1 : Spin) o).toReal * S o)
      = (m * lam) ^ n := by
    dsimp only [S]
    rw [hmean0, hmean1]
    norm_num
    ring
  have hmain : ((∑' o : Observation n,
        (observationLaw lam hlam offspring n (0 : Spin) o).toReal * S o)
      - (∑' o : Observation n,
        (observationLaw lam hlam offspring n (1 : Spin) o).toReal * S o)) ^ 2
      ≤ 2 * TheoremOS.Probability.pmfTV
          (observationLaw lam hlam offspring n (0 : Spin))
          (observationLaw lam hlam offspring n (1 : Spin)) * (Q0 + Q1) := by
    have := TheoremOS.Probability.sq_sub_le_pmfTV_mul_centred
      (p := observationLaw lam hlam offspring n (0 : Spin))
      (q := observationLaw lam hlam offspring n (1 : Spin))
      (S := S) (c := 0) hsum0 hsum1
    simpa only [Q0, Q1, sub_zero] using this
  have hTVnonneg : 0 ≤ TheoremOS.Probability.pmfTV
      (observationLaw lam hlam offspring n (0 : Spin))
      (observationLaw lam hlam offspring n (1 : Spin)) :=
    TheoremOS.Probability.pmfTV_nonneg _ _
  have hmain' : (m * lam) ^ (2 * n) ≤
      (4 * C * TheoremOS.Probability.pmfTV
        (observationLaw lam hlam offspring n (0 : Spin))
        (observationLaw lam hlam offspring n (1 : Spin))) * (m * lam) ^ (2 * n) := by
    calc (m * lam) ^ (2 * n)
        = ((m * lam) ^ n) ^ 2 := by
          rw [show 2 * n = n * 2 by ring, pow_mul]
      _ = ((∑' o : Observation n,
            (observationLaw lam hlam offspring n (0 : Spin) o).toReal * S o)
          - (∑' o : Observation n,
            (observationLaw lam hlam offspring n (1 : Spin) o).toReal * S o)) ^ 2 := by
          rw [hgap]
      _ ≤ 2 * TheoremOS.Probability.pmfTV
            (observationLaw lam hlam offspring n (0 : Spin))
            (observationLaw lam hlam offspring n (1 : Spin)) * (Q0 + Q1) := hmain
      _ ≤ 2 * TheoremOS.Probability.pmfTV
            (observationLaw lam hlam offspring n (0 : Spin))
            (observationLaw lam hlam offspring n (1 : Spin)) *
            (2 * C * (m * lam) ^ (2 * n)) := by
          gcongr
          linarith
      _ = (4 * C * TheoremOS.Probability.pmfTV
            (observationLaw lam hlam offspring n (0 : Spin))
            (observationLaw lam hlam offspring n (1 : Spin))) *
            (m * lam) ^ (2 * n) := by ring
  have hlam_ne : lam ≠ 0 := by
    intro h
    rw [h] at hKS
    norm_num at hKS
  have hbase : m * lam ≠ 0 := mul_ne_zero (ne_of_gt hmpos) hlam_ne
  have hpowpos : 0 < (m * lam) ^ (2 * n) := by
    rw [show 2 * n = n * 2 by ring, pow_mul]
    exact sq_pos_iff.mpr (pow_ne_zero n hbase)
  have hle : 1 ≤ 4 * C * TheoremOS.Probability.pmfTV
      (observationLaw lam hlam offspring n (0 : Spin))
      (observationLaw lam hlam offspring n (1 : Spin)) :=
    (le_mul_iff_one_le_left hpowpos).mp hmain'
  have hCpos : 0 < 4 * C := by linarith
  rw [div_le_iff₀ hCpos]
  nlinarith
theorem reconstructs_iff_uniform_advantage (lam : ℝ) (hlam : Admissible lam)
    (offspring : PMF ℕ) :
    Reconstructs lam hlam offspring ↔
      ∃ ε, 0 < ε ∧ ∀ ℓ, ε ≤ advantage lam hlam offspring ℓ := by
  have hAdv : advantage lam hlam offspring =
      fun ℓ => TheoremOS.Probability.reconAdvantage
        (fun i : Spin => observationLaw lam hlam offspring ℓ i) := by
    funext ℓ
    have h := TheoremOS.Probability.tsum_mul_posterior_div_eq_reconAdvantage
      (law := fun i : Spin => observationLaw lam hlam offspring ℓ i)
    rw [← h]
    simp only [advantage, jointWeight, marginalWeight, posterior, Fintype.card_fin]
    norm_num
  unfold Reconstructs
  rw [hAdv]
  exact (isBroadcastLaw_observationLaw lam hlam offspring).exists_pos_tendsto_iff
    (fun _ _ h => h) (fun _ _ _ h => h)

theorem reconstructs_of_uniform_advantage (lam : ℝ) (hlam : Admissible lam)
    (offspring : PMF ℕ)
    (h : ∃ ε, 0 < ε ∧ ∀ n, ε ≤ advantage lam hlam offspring n) :
    Reconstructs lam hlam offspring :=
  (reconstructs_iff_uniform_advantage lam hlam offspring).mpr h

theorem advantage_observationLaw_lower (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (m β : ℝ) (hm : ∑' k : ℕ, offspring k * (k : ℝ≥0∞) = ENNReal.ofReal m)
    (hβ : ∑' k : ℕ, offspring k * ((k * (k - 1) : ℕ) : ℝ≥0∞) = ENNReal.ofReal β)
    (C : ℝ) (hm1 : 1 < m) (hβ0 : 0 ≤ β) (hC0 : 4 / 9 ≤ C)
    (hC : 4 / 9 * (β * lam ^ 2) ≤ C * (m * (m * lam ^ 2 - 1)))
    (hKS : 1 < m * lam ^ 2)
    (X M : (n : ℕ) → Observation n → ℝ≥0∞)
    (hX : ∀ (n : ℕ) (s : Multiset (Observation n)), X (n + 1) s = (s.map (X n)).sum)
    (hM : ∀ (n : ℕ) (s : Multiset (Observation n)), M (n + 1) s = (s.map (M n)).sum)
    (hX0 : ∀ i : Spin, X 0 i = if i = (0 : Spin) then 1 else 0)
    (hM0 : ∀ i : Spin, M 0 i = 1)
    (n : ℕ) :
    1 / (12 * C) ≤ advantage lam hlam offspring n := by
  have hTV := pmfTV_observationLaw_lower lam hlam offspring m β hm hβ C hm1 hβ0 hC0 hC hKS
    X M hX hM hX0 hM0 n
  have hcard := TheoremOS.Probability.pmfTV_le_card_mul_reconAdvantage
    (law := fun i : Spin => observationLaw lam hlam offspring n i)
    (0 : Spin) (1 : Spin)
  have hbridge : advantage lam hlam offspring n =
      TheoremOS.Probability.reconAdvantage
        (fun i : Spin => observationLaw lam hlam offspring n i) := by
    have h := TheoremOS.Probability.tsum_mul_posterior_div_eq_reconAdvantage
      (law := fun i : Spin => observationLaw lam hlam offspring n i)
    rw [← h]
    simp only [advantage, jointWeight, marginalWeight, posterior, Fintype.card_fin]
    norm_num
  have hineq : 1 / (4 * C) ≤ 3 * advantage lam hlam offspring n := by
    rw [hbridge]
    calc 1 / (4 * C) ≤ TheoremOS.Probability.pmfTV
          (observationLaw lam hlam offspring n (0 : Spin))
          (observationLaw lam hlam offspring n (1 : Spin)) := hTV
      _ ≤ (Fintype.card Spin : ℝ) *
            TheoremOS.Probability.reconAdvantage
              (fun i : Spin => observationLaw lam hlam offspring n i) := hcard
      _ = 3 * TheoremOS.Probability.reconAdvantage
              (fun i : Spin => observationLaw lam hlam offspring n i) := by
          norm_num [Spin]
  have hCpos : 0 < C := by linarith
  have h4C : 0 < 4 * C := by positivity
  have h12C : 0 < 12 * C := by positivity
  have hineq' : 1 ≤ (3 * advantage lam hlam offspring n) * (4 * C) :=
    (div_le_iff₀ h4C).mp hineq
  rw [div_le_iff₀ h12C]
  nlinarith
lemma exists_C_of_KS (m β lam : ℝ) (hm1 : 1 < m) (hβ0 : 0 ≤ β)
    (hKS : 1 < m * lam ^ 2) :
    ∃ C : ℝ, 4 / 9 ≤ C ∧
      4 / 9 * (β * lam ^ 2) ≤ C * (m * (m * lam ^ 2 - 1)) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm1
  have hD : 0 < m * (m * lam ^ 2 - 1) := by
    have : 0 < m * lam ^ 2 - 1 := by linarith
    exact mul_pos hm0 this
  refine ⟨4 / 9 + (4 / 9) * (β * lam ^ 2) / (m * (m * lam ^ 2 - 1)), ?_, ?_⟩
  · have hx : 0 ≤ (4 / 9) * (β * lam ^ 2) / (m * (m * lam ^ 2 - 1)) :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg hβ0 (sq_nonneg lam))) hD.le
    linarith
  · have hx : (4 / 9) * (β * lam ^ 2) / (m * (m * lam ^ 2 - 1)) *
        (m * (m * lam ^ 2 - 1)) = (4 / 9) * (β * lam ^ 2) :=
      div_mul_cancel₀ _ hD.ne'
    rw [add_mul]
    have hDnon : 0 ≤ 4 / 9 * (m * (m * lam ^ 2 - 1)) :=
      mul_nonneg (by norm_num) hD.le
    nlinarith
lemma lam_sq_le_one {lam : ℝ} (hlam : Admissible lam) : lam ^ 2 ≤ 1 := by
  nlinarith [hlam.1, hlam.2, sq_nonneg lam]
lemma natCast_mul_pred (b : ℕ) :
    ((b * (b - 1) : ℕ) : ℝ) = (b : ℝ) * ((b : ℝ) - 1) := by
  rcases b with _ | b
  · norm_num
  · push_cast [Nat.succ_mul]
    ring
lemma one_lt_nat_of_KS {b : ℕ} {lam : ℝ} (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : 1 < (b:ℝ) := by
  have hsq := lam_sq_le_one hlam
  have hbpos : 0 < (b:ℝ) := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; norm_num at hKS
    · exact_mod_cast h
  have hb1 : (b:ℝ) * lam^2 ≤ (b:ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hsq hbpos.le
  linarith
lemma one_lt_nnreal_of_KS {d : ℝ≥0} {lam : ℝ} (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ) * lam^2) : 1 < (d:ℝ) := by
  have hsq := lam_sq_le_one hlam
  have hdpos : 0 < (d:ℝ) := by
    rcases eq_or_lt_of_le d.coe_nonneg with h | h
    · rw [← h] at hKS; norm_num at hKS
    · exact h
  have hd1 : (d:ℝ) * lam^2 ≤ (d:ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hsq hdpos.le
  linarith
lemma pure_mean (b : ℕ) :
    (∑' k : ℕ, (PMF.pure b) k * (k : ℝ≥0∞)) = ENNReal.ofReal (b:ℝ) := by
  rw [TheoremOS.Probability.tsum_pure_mul_natCast b, ENNReal.ofReal_natCast]
lemma pure_factorial_moment (b : ℕ) :
    (∑' k : ℕ, (PMF.pure b) k * ((k * (k - 1) : ℕ) : ℝ≥0∞))
      = ENNReal.ofReal ((b:ℝ) * ((b:ℝ) - 1)) := by
  rw [TheoremOS.Probability.tsum_pure_mul b (fun k => ((k * (k - 1) : ℕ) : ℝ≥0∞)),
    ← ENNReal.ofReal_natCast, natCast_mul_pred]
lemma poisson_mean (d : ℝ≥0) :
    (∑' k : ℕ, (poissonPMF d) k * (k : ℝ≥0∞)) = ENNReal.ofReal (d:ℝ) := by
  have h := TheoremOS.Probability.tsum_ofReal_poissonWeight_mul d.coe_nonneg
  convert h using 2
  funext k
  rfl
lemma poisson_factorial_moment (d : ℝ≥0) :
    (∑' k : ℕ, (poissonPMF d) k * ((k * (k - 1) : ℕ) : ℝ≥0∞))
      = ENNReal.ofReal ((d:ℝ) * (d:ℝ)) := by
  have h := TheoremOS.Probability.tsum_ofReal_poissonWeight_mul_descFactorial d.coe_nonneg
  have hone : ENNReal.ofReal ((d:ℝ) ^ 2) = ENNReal.ofReal ((d:ℝ) * (d:ℝ)) := by
    rw [pow_two]
  rw [hone] at h
  rw [← h]
  congr 2
lemma regular_advantage_uniform_lower (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) :
    ∃ ε, 0 < ε ∧ ∀ n, ε ≤ advantage lam hlam (PMF.pure b) n := by
  obtain ⟨X, M, hX, hM, hX0, hM0⟩ := exists_census_pair
  have hm1 : 1 < (b:ℝ) := one_lt_nat_of_KS hlam hKS
  have hβ0 : 0 ≤ (b:ℝ) * ((b:ℝ) - 1) := by nlinarith
  obtain ⟨C, hC0, hC⟩ := exists_C_of_KS (b:ℝ) ((b:ℝ) * ((b:ℝ) - 1)) lam hm1 hβ0 hKS
  have hCpos : 0 < C := by linarith
  exact ⟨1 / (12 * C), by positivity, fun n =>
    advantage_observationLaw_lower lam hlam (PMF.pure b) (b:ℝ) ((b:ℝ) * ((b:ℝ) - 1))
      (pure_mean b) (pure_factorial_moment b) C hm1 hβ0 hC0 hC hKS X M hX hM hX0 hM0 n⟩
lemma poisson_advantage_uniform_lower (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) :
    ∃ ε, 0 < ε ∧ ∀ n, ε ≤ advantage lam hlam (poissonPMF d) n := by
  obtain ⟨X, M, hX, hM, hX0, hM0⟩ := exists_census_pair
  have hm1 : 1 < (d:ℝ) := one_lt_nnreal_of_KS hlam hKS
  have hβ0 : 0 ≤ (d:ℝ) * (d:ℝ) := mul_self_nonneg _
  obtain ⟨C, hC0, hC⟩ := exists_C_of_KS (d:ℝ) ((d:ℝ) * (d:ℝ)) lam hm1 hβ0 hKS
  have hCpos : 0 < C := by linarith
  exact ⟨1 / (12 * C), by positivity, fun n =>
    advantage_observationLaw_lower lam hlam (poissonPMF d) (d:ℝ) ((d:ℝ) * (d:ℝ))
      (poisson_mean d) (poisson_factorial_moment d) C hm1 hβ0 hC0 hC hKS X M hX hM hX0 hM0 n⟩
end ThreeState.TreeClauses

open scoped Topology
namespace ThreeState.TreeClauses.Tree

theorem regular_reconstructs_above_KS (b : ℕ) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (b:ℝ)*lam^2) : Reconstructs lam hlam (PMF.pure b) := by
  obtain ⟨eps, heps, hlow⟩ := regular_advantage_uniform_lower b lam hlam hKS
  exact reconstructs_of_uniform_advantage lam hlam (PMF.pure b) ⟨eps, heps, hlow⟩
theorem poisson_reconstructs_above_KS (d : ℝ≥0) (lam : ℝ) (hlam : Admissible lam)
    (hKS : 1 < (d:ℝ)*lam^2) : Reconstructs lam hlam (poissonPMF d) := by
  obtain ⟨eps, heps, hlow⟩ := poisson_advantage_uniform_lower d lam hlam hKS
  exact reconstructs_of_uniform_advantage lam hlam (poissonPMF d) ⟨eps, heps, hlow⟩
end ThreeState.TreeClauses.Tree

end

end OAI
