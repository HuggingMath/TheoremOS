import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace IsingPerceptron

def gaussianTransform (s d : ℝ) (U : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d = 0 then ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1
  else (Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
    ∂gaussianReal 0 1)) / d

structure Partition where
  levels : ℕ
  positive : 0 < levels
  cut : Fin (levels + 1) → ℝ
  ordered : StrictMono cut
  first : cut ⟨0, Nat.zero_lt_succ levels⟩ = 0
  last : cut ⟨levels, Nat.lt_succ_self levels⟩ = 1

structure FieldStep where
  partition : Partition
  value : Fin partition.levels → ℝ
  nonneg : ∀ i, 0 ≤ value i
  ordered : Monotone value

 
lemma gaussianTransform_abs_le (s d K : ℝ) {U : ℝ → ℝ} (hU : Continuous U)
    (hUK : ∀ x, |U x| ≤ K) : ∀ x, |gaussianTransform s d U x| ≤ K := by
  intro x
  by_cases hd : d = 0
  · simp only [gaussianTransform, hd, ite_true]
    have hcont : Continuous fun z : ℝ => U (x + Real.sqrt s * z) := by fun_prop
    have hint : Integrable (fun z : ℝ => U (x + Real.sqrt s * z)) (gaussianReal 0 1) :=
      Integrable.of_bound hcont.aestronglyMeasurable K
        (Filter.Eventually.of_forall (fun z => by
          simpa [Real.norm_eq_abs] using hUK (x + Real.sqrt s * z)))
    have h1 : ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1 ≤ K := by
      calc
        _ ≤ ∫ _z : ℝ, K ∂gaussianReal 0 1 :=
          integral_mono hint (integrable_const K) (fun z => (abs_le.mp (hUK _)).2)
        _ = K := by simp
    have h2 : -K ≤ ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1 := by
      calc
        -K = ∫ _z : ℝ, -K ∂gaussianReal 0 1 := by simp
        _ ≤ _ := integral_mono (integrable_const (-K)) hint
          (fun z => (abs_le.mp (hUK _)).1)
    exact abs_le.mpr ⟨h2, h1⟩
  · simp only [gaussianTransform, hd, ite_false]
    have hcont : Continuous fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z)) := by
      fun_prop
    have hbound : ∀ z : ℝ, |Real.exp (d * U (x + Real.sqrt s * z))| ≤ Real.exp (|d| * K) := by
      intro z
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        d * U (x + Real.sqrt s * z) ≤ |d * U (x + Real.sqrt s * z)| := le_abs_self _
        _ = |d| * |U (x + Real.sqrt s * z)| := abs_mul _ _
        _ ≤ |d| * K := mul_le_mul_of_nonneg_left (hUK _) (abs_nonneg _)
    have hint : Integrable (fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z)))
        (gaussianReal 0 1) :=
      Integrable.of_bound hcont.aestronglyMeasurable (Real.exp (|d| * K))
        (Filter.Eventually.of_forall hbound)
    have hupp : ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 ≤
        Real.exp (|d| * K) := by
      calc
        _ ≤ ∫ _z : ℝ, Real.exp (|d| * K) ∂gaussianReal 0 1 :=
          integral_mono hint (integrable_const _) (fun z => (abs_le.mp (hbound z)).2)
        _ = Real.exp (|d| * K) := by simp
    have hlow : Real.exp (-(|d| * K)) ≤
        ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
      calc
        Real.exp (-(|d| * K)) = ∫ _z : ℝ, Real.exp (-(|d| * K)) ∂gaussianReal 0 1 := by simp
        _ ≤ _ := by
          apply integral_mono (integrable_const _) hint
          intro z
          apply Real.exp_le_exp.mpr
          have hz : |d * U (x + Real.sqrt s * z)| ≤ |d| * K := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hUK _) (abs_nonneg _)
          exact (abs_le.mp hz).1
    have hIpos : 0 < ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
      lt_of_lt_of_le (Real.exp_pos _) hlow
    have hlog_upper : Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
        ∂gaussianReal 0 1) ≤ |d| * K := by
      calc
        Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)
            ≤ Real.log (Real.exp (|d| * K)) := Real.log_le_log hIpos hupp
        _ = |d| * K := Real.log_exp _
    have hlog_lower : -(|d| * K) ≤ Real.log
        (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) := by
      calc
        -(|d| * K) = Real.log (Real.exp (-(|d| * K))) := by rw [Real.log_exp]
        _ ≤ Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) :=
          Real.log_le_log (Real.exp_pos _) hlow
    have hlogabs : |Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
        ∂gaussianReal 0 1)| ≤ |d| * K :=
      abs_le.mpr ⟨hlog_lower, hlog_upper⟩
    rw [abs_div]
    rw [div_le_iff₀ (abs_pos.mpr hd)]
    calc
      |Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)|
          ≤ |d| * K := hlogabs
      _ = K * |d| := by ring
lemma gaussianTransform_abs_le_of_bound (s d K : ℝ) {U : ℝ → ℝ}
    (hUK : ∀ x, |U x| ≤ K) : ∀ x, |gaussianTransform s d U x| ≤ K := by
  have hK : 0 ≤ K := le_trans (abs_nonneg (U 0)) (hUK 0)
  intro x
  by_cases hd : d = 0
  · simp only [gaussianTransform, hd, ite_true]
    by_cases hmeas : AEStronglyMeasurable
        (fun z : ℝ => U (x + Real.sqrt s * z)) (gaussianReal 0 1)
    · have hint : Integrable (fun z : ℝ => U (x + Real.sqrt s * z)) (gaussianReal 0 1) :=
        Integrable.of_bound hmeas K
          (Filter.Eventually.of_forall (fun z => by
            simpa [Real.norm_eq_abs] using hUK (x + Real.sqrt s * z)))
      have h1 : ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1 ≤ K := by
        calc
          _ ≤ ∫ _z : ℝ, K ∂gaussianReal 0 1 :=
            integral_mono hint (integrable_const K) (fun z => (abs_le.mp (hUK _)).2)
          _ = K := by simp
      have h2 : -K ≤ ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1 := by
        calc
          -K = ∫ _z : ℝ, -K ∂gaussianReal 0 1 := by simp
          _ ≤ _ := integral_mono (integrable_const (-K)) hint
            (fun z => (abs_le.mp (hUK _)).1)
      exact abs_le.mpr ⟨h2, h1⟩
    · rw [integral_non_aestronglyMeasurable hmeas]
      simpa using hK
  · simp only [gaussianTransform, hd, ite_false]
    by_cases hmeas : AEStronglyMeasurable
        (fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z))) (gaussianReal 0 1)
    · have hbound : ∀ z : ℝ, |Real.exp (d * U (x + Real.sqrt s * z))| ≤
          Real.exp (|d| * K) := by
        intro z
        rw [abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        calc
          d * U (x + Real.sqrt s * z) ≤ |d * U (x + Real.sqrt s * z)| := le_abs_self _
          _ = |d| * |U (x + Real.sqrt s * z)| := abs_mul _ _
          _ ≤ |d| * K := mul_le_mul_of_nonneg_left (hUK _) (abs_nonneg _)
      have hint : Integrable (fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z)))
          (gaussianReal 0 1) :=
        Integrable.of_bound hmeas (Real.exp (|d| * K))
          (Filter.Eventually.of_forall hbound)
      have hupp : ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 ≤
          Real.exp (|d| * K) := by
        calc
          _ ≤ ∫ _z : ℝ, Real.exp (|d| * K) ∂gaussianReal 0 1 :=
            integral_mono hint (integrable_const _) (fun z => (abs_le.mp (hbound z)).2)
          _ = Real.exp (|d| * K) := by simp
      have hlow : Real.exp (-(|d| * K)) ≤
          ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
        calc
          Real.exp (-(|d| * K)) = ∫ _z : ℝ, Real.exp (-(|d| * K)) ∂gaussianReal 0 1 := by simp
          _ ≤ _ := by
            apply integral_mono (integrable_const _) hint
            intro z
            apply Real.exp_le_exp.mpr
            have hz : |d * U (x + Real.sqrt s * z)| ≤ |d| * K := by
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hUK _) (abs_nonneg _)
            exact (abs_le.mp hz).1
      have hIpos : 0 < ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
        lt_of_lt_of_le (Real.exp_pos _) hlow
      have hlog_upper : Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
          ∂gaussianReal 0 1) ≤ |d| * K := by
        calc
          Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)
              ≤ Real.log (Real.exp (|d| * K)) := Real.log_le_log hIpos hupp
          _ = |d| * K := Real.log_exp _
      have hlog_lower : -(|d| * K) ≤ Real.log
          (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) := by
        calc
          -(|d| * K) = Real.log (Real.exp (-(|d| * K))) := by rw [Real.log_exp]
          _ ≤ Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) :=
            Real.log_le_log (Real.exp_pos _) hlow
      have hlogabs : |Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z))
          ∂gaussianReal 0 1)| ≤ |d| * K :=
        abs_le.mpr ⟨hlog_lower, hlog_upper⟩
      rw [abs_div]
      rw [div_le_iff₀ (abs_pos.mpr hd)]
      calc
        |Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)|
            ≤ |d| * K := hlogabs
        _ = K * |d| := by ring
    · rw [integral_non_aestronglyMeasurable hmeas]
      simp only [Real.log_zero, zero_div, abs_zero]
      exact hK
lemma foldr_gaussianTransform_abs_le (L : List (ℝ × ℝ)) (K : ℝ) {V : ℝ → ℝ}
    (hV : ∀ x, |V x| ≤ K) :
    ∀ x, |L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V x| ≤ K := by
  induction L with
  | nil => simpa using hV
  | cons a L ih =>
      intro x
      simpa [List.foldr_cons] using gaussianTransform_abs_le_of_bound a.1 a.2 K ih x
def stepAt (h : FieldStep) (i : ℕ) : ℝ :=
  if hi : i < h.partition.levels then h.value ⟨i, hi⟩ else 0

 

def stepFunction (h : FieldStep) (u : ℝ) : ℝ :=
  ∑ i : Fin h.partition.levels,
    if h.partition.cut i.castSucc < u ∧ u < h.partition.cut i.succ then h.value i else 0

 
def fieldRecursion (h : FieldStep) : ℝ :=
  let k := h.partition.levels
  let increments := List.ofFn (fun i : Fin k =>
    (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
      h.partition.cut i.castSucc))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U)
    (fun x => Real.log (Real.cosh x) - stepAt h (k - 1) / 2) 0

def pathMeasure : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

 
structure OverlapPath where
  val : ℝ →ₘ[pathMeasure] ℝ
  admissible : ∃ q : ℝ → ℝ,
    (q =ᵐ[pathMeasure] val) ∧ MonotoneOn q (Set.Ioo 0 1) ∧
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, q u ∈ Set.Icc (0 : ℝ) 1

 
def cellAverage (q : OverlapPath) (k i : ℕ) : ℝ :=
  (k : ℝ) * ∫ u in Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k),
    q.val u ∂pathMeasure

 

def uniformPattern (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) : ℝ :=
  let k := n + 1
  let levelVal := fun i => if i < k then cellAverage q k i else 1
  let increments := List.ofFn (fun i : Fin (k + 1) =>
    (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)), (i : ℝ) / k))
  increments.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) f 0

 

lemma uniformPattern_abs_le (f : ℝ → ℝ) (K : ℝ) (_hf : Continuous f)
    (hK : ∀ x, |f x| ≤ K) (q : OverlapPath) (n : ℕ) :
    |uniformPattern f q n| ≤ K := by
  simpa [uniformPattern] using
    foldr_gaussianTransform_abs_le
      (List.ofFn (fun i : Fin (n + 2) =>
        let k := n + 1
        let levelVal := fun j => if j < k then cellAverage q k j else 1
        (levelVal i - (if i.val = 0 then 0 else levelVal (i.val - 1)),
          (i : ℝ) / k))) K hK 0
def patternFunctional (f : ℝ → ℝ) (q : OverlapPath) : ℝ :=
  Filter.limUnder atTop (uniformPattern f q)

 

def isingEntropy (q : OverlapPath) : EReal :=
  ⨆ h : FieldStep,
    ((fieldRecursion h + (∫ u, stepFunction h u * q.val u ∂pathMeasure) / 2 : ℝ) : EReal)

def isingEntropyWitnessPartition : Partition where
  levels := 1
  positive := by norm_num
  cut := fun i : Fin (1 + 1) => (i.val : ℝ)
  ordered := by
    intro i j hij
    exact Nat.cast_lt.mpr hij
  first := by simp
  last := by simp
def isingEntropyWitnessFieldStep : FieldStep where
  partition := isingEntropyWitnessPartition
  value := fun _ => 0
  nonneg := by intro i; rfl
  ordered := by intro i j _; rfl
lemma stepAt_isingEntropyWitnessFieldStep (i : ℕ) :
    stepAt isingEntropyWitnessFieldStep i = 0 := by
  unfold stepAt
  split_ifs <;> rfl
lemma stepFunction_isingEntropyWitnessFieldStep (u : ℝ) :
    stepFunction isingEntropyWitnessFieldStep u = 0 := by
  unfold stepFunction
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs <;> rfl
lemma fieldRecursion_isingEntropyWitnessFieldStep :
    fieldRecursion isingEntropyWitnessFieldStep = 0 := by
  simp [fieldRecursion, isingEntropyWitnessFieldStep, isingEntropyWitnessPartition,
    gaussianTransform, stepAt, Real.log_one]
theorem isingEntropy_nonneg (q : OverlapPath) : (0 : EReal) ≤ isingEntropy q := by
  unfold isingEntropy
  refine le_iSup_of_le (f := fun h : FieldStep =>
    ((fieldRecursion h + (∫ u, stepFunction h u * q.val u ∂pathMeasure) / 2 : ℝ) : EReal))
    isingEntropyWitnessFieldStep ?_
  simp [fieldRecursion_isingEntropyWitnessFieldStep,
    stepFunction_isingEntropyWitnessFieldStep]
def variationalValue (α : ℝ) (f : ℝ → ℝ) : EReal :=
  ⨅ q : OverlapPath, (α * patternFunctional f q : ℝ) + isingEntropy q

lemma integral_exp_mul_gaussianReal_one (t : ℝ) :
    ∫ z, Real.exp (t * z) ∂gaussianReal 0 1 = Real.exp (t ^ 2 / 2) := by
  have h := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := 1)) t
  simpa [ProbabilityTheory.mgf] using h
lemma integrable_exp_pos_affine (x s : ℝ) :
    Integrable (fun z : ℝ => Real.exp (x + Real.sqrt s * z)) (gaussianReal 0 1) := by
  have h : Integrable (fun z : ℝ => Real.exp (Real.sqrt s * z)) (gaussianReal 0 1) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal _
  have h2 : Integrable (fun z : ℝ => Real.exp x * Real.exp (Real.sqrt s * z))
      (gaussianReal 0 1) := h.const_mul _
  refine h2.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [← Real.exp_add]
lemma integrable_exp_neg_affine (x s : ℝ) :
    Integrable (fun z : ℝ => Real.exp (-(x + Real.sqrt s * z))) (gaussianReal 0 1) := by
  have h : Integrable (fun z : ℝ => Real.exp ((-Real.sqrt s) * z)) (gaussianReal 0 1) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal _
  have h2 : Integrable (fun z : ℝ => Real.exp (-x) * Real.exp ((-Real.sqrt s) * z))
      (gaussianReal 0 1) := h.const_mul _
  refine h2.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [← Real.exp_add]
  ring_nf
lemma integral_exp_affine {s : ℝ} (hs : 0 ≤ s) (t x : ℝ) :
    ∫ z, Real.exp (x + t * z) ∂gaussianReal 0 1 = Real.exp x * Real.exp (t ^ 2 / 2) := by
  have h := integral_exp_mul_gaussianReal_one t
  calc ∫ z, Real.exp (x + t * z) ∂gaussianReal 0 1
      = ∫ z, Real.exp x * Real.exp (t * z) ∂gaussianReal 0 1 := by
        congr 1 with z; rw [Real.exp_add]
    _ = Real.exp x * ∫ z, Real.exp (t * z) ∂gaussianReal 0 1 := integral_const_mul _ _
    _ = Real.exp x * Real.exp (t ^ 2 / 2) := by rw [h]
lemma integrable_cosh_gaussianReal (x s : ℝ) :
    Integrable (fun z : ℝ => Real.cosh (x + Real.sqrt s * z)) (gaussianReal 0 1) := by
  have h1 := integrable_exp_pos_affine x s
  have h2 := integrable_exp_neg_affine x s
  have h3 : Integrable (fun z : ℝ => Real.exp (x + Real.sqrt s * z)
      + Real.exp (-(x + Real.sqrt s * z))) (gaussianReal 0 1) := h1.add h2
  have h4 := h3.const_mul ((2:ℝ)⁻¹)
  refine h4.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Real.cosh_eq]
  ring
lemma integral_cosh_gaussianReal {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    ∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1
      = Real.cosh x * Real.exp (s / 2) := by
  have hsp : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs
  have h1 := integrable_exp_pos_affine x s
  have h2 := integrable_exp_neg_affine x s
  have e1 : ∫ z, Real.exp (x + Real.sqrt s * z) ∂gaussianReal 0 1
      = Real.exp x * Real.exp (s / 2) := by
    rw [integral_exp_affine hs, hsp]
  have e2 : ∫ z, Real.exp (-(x + Real.sqrt s * z)) ∂gaussianReal 0 1
      = Real.exp (-x) * Real.exp (s / 2) := by
    have h := integral_exp_mul_gaussianReal_one (-Real.sqrt s)
    calc ∫ z, Real.exp (-(x + Real.sqrt s * z)) ∂gaussianReal 0 1
        = ∫ z, Real.exp (-x) * Real.exp ((-Real.sqrt s) * z) ∂gaussianReal 0 1 := by
          congr 1 with z; rw [← Real.exp_add]; ring_nf
      _ = Real.exp (-x) * ∫ z, Real.exp ((-Real.sqrt s) * z) ∂gaussianReal 0 1 :=
          integral_const_mul _ _
      _ = Real.exp (-x) * Real.exp (((-Real.sqrt s)) ^ 2 / 2) := by rw [h]
      _ = Real.exp (-x) * Real.exp (s / 2) := by
          rw [show ((-Real.sqrt s)) ^ 2 = s by rw [neg_sq, hsp]]
  calc ∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1
      = ∫ z, (Real.exp (x + Real.sqrt s * z) + Real.exp (-(x + Real.sqrt s * z))) / 2
          ∂gaussianReal 0 1 := by
        congr 1 with z
        rw [Real.cosh_eq]
    _ = (∫ z, (Real.exp (x + Real.sqrt s * z) + Real.exp (-(x + Real.sqrt s * z)))
          ∂gaussianReal 0 1) / 2 := by rw [integral_div]
    _ = ((∫ z, Real.exp (x + Real.sqrt s * z) ∂gaussianReal 0 1)
          + (∫ z, Real.exp (-(x + Real.sqrt s * z)) ∂gaussianReal 0 1)) / 2 := by
        rw [integral_add h1 h2]
    _ = Real.cosh x * Real.exp (s / 2) := by
        rw [e1, e2, Real.cosh_eq]
        ring
lemma exp_mul_le_cosh_rpow {d w : ℝ} (hd : 0 ≤ d) {U : ℝ → ℝ}
    (hU : ∀ y, U y ≤ Real.log (Real.cosh y) - w / 2) (y : ℝ) :
    Real.exp (d * U y) ≤ (Real.cosh y) ^ d * Real.exp (-(d * w / 2)) := by
  have hcosh_pos : 0 < Real.cosh y := Real.cosh_pos y
  have h1 : d * U y ≤ d * (Real.log (Real.cosh y) - w / 2) :=
    mul_le_mul_of_nonneg_left (hU y) hd
  have h2 : Real.exp (d * U y) ≤ Real.exp (d * (Real.log (Real.cosh y) - w / 2)) :=
    Real.exp_le_exp.mpr h1
  have h3 : Real.exp (d * (Real.log (Real.cosh y) - w / 2))
      = (Real.cosh y) ^ d * Real.exp (-(d * w / 2)) := by
    rw [Real.rpow_def_of_pos hcosh_pos]
    rw [show d * (Real.log (Real.cosh y) - w / 2)
      = Real.log (Real.cosh y) * d + (-(d * w / 2)) by ring]
    rw [Real.exp_add]
  rw [← h3]
  exact h2
lemma integrable_cosh_rpow_gaussianReal {s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (x : ℝ) :
    Integrable (fun z : ℝ => (Real.cosh (x + Real.sqrt s * z)) ^ d) (gaussianReal 0 1) := by
  have hcosh := integrable_cosh_gaussianReal x s
  have hmeas : AEStronglyMeasurable (fun z : ℝ => (Real.cosh (x + Real.sqrt s * z)) ^ d)
      (gaussianReal 0 1) := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  refine Integrable.mono hcosh hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have hpos : 0 < Real.cosh (x + Real.sqrt s * z) := Real.cosh_pos _
  rw [abs_of_pos (Real.rpow_pos_of_pos hpos d), abs_of_pos hpos]
  calc (Real.cosh (x + Real.sqrt s * z)) ^ d
      ≤ (Real.cosh (x + Real.sqrt s * z)) ^ (1:ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Real.one_le_cosh _
        · exact hd1
    _ = Real.cosh (x + Real.sqrt s * z) := Real.rpow_one _
lemma integrable_exp_mul_u_gaussianReal {s d w M : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) - w / 2) (x : ℝ) :
    Integrable (fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z))) (gaussianReal 0 1) := by
  have hcosh_rpow := integrable_cosh_rpow_gaussianReal hs hd hd1 x
  have hbound_int : Integrable (fun z : ℝ => (Real.cosh (x + Real.sqrt s * z)) ^ d
      * Real.exp (-(d * w / 2))) (gaussianReal 0 1) := hcosh_rpow.mul_const _
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (d * U (x + Real.sqrt s * z)))
      (gaussianReal 0 1) := by
    have h2 : Measurable fun z : ℝ => U (x + Real.sqrt s * z) :=
      hUmeas.comp (by fun_prop)
    exact (Real.measurable_exp.comp (h2.const_mul d)).aestronglyMeasurable
  refine Integrable.mono' hbound_int hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_mul_le_cosh_rpow hd hUup _
lemma integrable_cosh_mul_exp_gaussianReal {s d w : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (x : ℝ) :
    Integrable (fun z : ℝ => (Real.cosh (x + Real.sqrt s * z)) ^ d
      * Real.exp (-(d * w / 2))) (gaussianReal 0 1) := by
  have hcosh_rpow := integrable_cosh_rpow_gaussianReal hs hd hd1 x
  exact hcosh_rpow.mul_const _
lemma jensen_step_pos {s d w M : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U) (hUlow : ∀ x, -M ≤ U x)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) - w / 2) (x : ℝ) :
    ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1
      ≤ (Real.cosh x) ^ d * Real.exp (s * d / 2 - d * w / 2) := by
  have hcosh_int : ∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1
      = Real.cosh x * Real.exp (s / 2) := integral_cosh_gaussianReal hs x
  have hcosh_int_meas : Integrable (fun z : ℝ => Real.cosh (x + Real.sqrt s * z))
      (gaussianReal 0 1) := integrable_cosh_gaussianReal x s
  have hptw : ∀ z, Real.exp (d * U (x + Real.sqrt s * z))
      ≤ (Real.cosh (x + Real.sqrt s * z)) ^ d * Real.exp (-(d * w / 2)) :=
    fun z => exp_mul_le_cosh_rpow hd.le hUup _
  have hJensen : (∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1) ^ d
      ≥ ∫ z, (Real.cosh (x + Real.sqrt s * z)) ^ d ∂gaussianReal 0 1 := by
    have hconcave : ConcaveOn ℝ (Set.Ici 0) (fun y : ℝ => y ^ d) :=
      Real.concaveOn_rpow hd.le hd1
    have hcont : ContinuousOn (fun y : ℝ => y ^ d) (Set.Ici 0) := by
      intro y hy
      exact (Real.continuousAt_rpow_const y d (Or.inr hd.le)).continuousWithinAt
    have hmem : ∀ᵐ z ∂gaussianReal 0 1, Real.cosh (x + Real.sqrt s * z) ∈ Set.Ici (0:ℝ) :=
      Filter.Eventually.of_forall (fun z => (Real.cosh_pos _).le)
    have hint_rpow : Integrable (fun z : ℝ => (Real.cosh (x + Real.sqrt s * z)) ^ d)
        (gaussianReal 0 1) := integrable_cosh_rpow_gaussianReal hs hd.le hd1 x
    simpa only [Function.comp_apply] using
      (ConcaveOn.le_map_integral hconcave hcont isClosed_Ici hmem hcosh_int_meas hint_rpow)
  have h_exp_int := integrable_exp_mul_u_gaussianReal (M := M) hs hd.le hd1 hUmeas hUup x
  have h_bound_int := integrable_cosh_mul_exp_gaussianReal hs hd.le hd1 (w := w) x
  calc ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1
      ≤ ∫ z, (Real.cosh (x + Real.sqrt s * z)) ^ d * Real.exp (-(d * w / 2))
          ∂gaussianReal 0 1 := integral_mono h_exp_int h_bound_int hptw
    _ = (∫ z, (Real.cosh (x + Real.sqrt s * z)) ^ d ∂gaussianReal 0 1)
          * Real.exp (-(d * w / 2)) := integral_mul_const _ _
    _ ≤ (∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1) ^ d
          * Real.exp (-(d * w / 2)) := by
        apply mul_le_mul_of_nonneg_right hJensen (Real.exp_pos _).le
    _ = (Real.cosh x * Real.exp (s / 2)) ^ d * Real.exp (-(d * w / 2)) := by rw [hcosh_int]
    _ = (Real.cosh x) ^ d * Real.exp (s * d / 2 - d * w / 2) := by
        rw [Real.mul_rpow (Real.cosh_pos x).le (Real.exp_pos (s/2)).le]
        rw [show (Real.exp (s / 2)) ^ d = Real.exp (s / 2 * d) by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
lemma integrable_shift_of_bounds {s w M : ℝ} {U : ℝ → ℝ} (hUmeas : Measurable U)
    (hUlow : ∀ y, -M ≤ U y) (hUup : ∀ y, U y ≤ Real.log (Real.cosh y) - w / 2)
    (hwM : -w / 2 ≤ M) (x : ℝ) :
    Integrable (fun z : ℝ => U (x + Real.sqrt s * z)) (gaussianReal 0 1) := by
  have hc : Integrable (fun z : ℝ => Real.cosh (x + Real.sqrt s * z)) (gaussianReal 0 1) :=
    integrable_cosh_gaussianReal x s
  have hmono : Integrable (fun z : ℝ => M + Real.cosh (x + Real.sqrt s * z)) (gaussianReal 0 1) := by
    have := (integrable_const (μ := gaussianReal 0 1) M).add hc
    simpa [add_comm] using this
  have hmeas : AEStronglyMeasurable (fun z : ℝ => U (x + Real.sqrt s * z)) (gaussianReal 0 1) :=
    (hUmeas.comp (by fun_prop)).aestronglyMeasurable
  refine Integrable.mono' hmono hmeas (Filter.Eventually.of_forall (fun z => ?_))
  have hlog_le : Real.log (Real.cosh (x + Real.sqrt s * z)) ≤ Real.cosh (x + Real.sqrt s * z) := by
    have h1 : Real.log (Real.cosh (x + Real.sqrt s * z)) ≤ Real.cosh (x + Real.sqrt s * z) - 1 :=
      Real.log_le_sub_one_of_pos (Real.cosh_pos _)
    linarith
  have hpos : (0:ℝ) ≤ Real.cosh (x + Real.sqrt s * z) := (Real.cosh_pos _).le
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := hUlow (x + Real.sqrt s * z); linarith
  · have := hUup (x + Real.sqrt s * z); linarith
lemma integrable_exp_shift_of_bounds {s w M : ℝ} {U : ℝ → ℝ} (hUmeas : Measurable U)
    (hUlow : ∀ y, -M ≤ U y) (hUup : ∀ y, U y ≤ Real.log (Real.cosh y) - w / 2) (x : ℝ) :
    Integrable (fun z : ℝ => Real.exp (U (x + Real.sqrt s * z))) (gaussianReal 0 1) := by
  have hc : Integrable (fun z : ℝ => Real.cosh (x + Real.sqrt s * z) * Real.exp (-(w / 2)))
      (gaussianReal 0 1) := (integrable_cosh_gaussianReal x s).mul_const _
  have hmeas : AEStronglyMeasurable (fun z : ℝ => Real.exp (U (x + Real.sqrt s * z)))
      (gaussianReal 0 1) :=
    (Real.measurable_exp.comp (hUmeas.comp (by fun_prop))).aestronglyMeasurable
  refine Integrable.mono' hc hmeas (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa using exp_mul_le_cosh_rpow (d := 1) zero_le_one hUup (x + Real.sqrt s * z)
lemma integral_le_log_integral_exp {s w M : ℝ} {U : ℝ → ℝ} (hUmeas : Measurable U)
    (hUlow : ∀ y, -M ≤ U y) (hUup : ∀ y, U y ≤ Real.log (Real.cosh y) - w / 2)
    (hwM : -w / 2 ≤ M) (x : ℝ) :
    ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1
      ≤ Real.log (∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) := by
  have hUint := integrable_shift_of_bounds (s := s) (w := w) (M := M) hUmeas hUlow hUup hwM x
  have hGint := integrable_exp_shift_of_bounds (s := s) (w := w) (M := M) hUmeas hUlow hUup x
  set A : ℝ := ∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 with hA
  have hApos : 0 < A := by
    have hconst : Integrable (fun _ : ℝ => Real.exp (-M)) (gaussianReal 0 1) := integrable_const _
    have hle : (∫ _z : ℝ, Real.exp (-M) ∂gaussianReal 0 1) ≤ A := by
      rw [hA]
      apply integral_mono hconst hGint
      intro z; exact Real.exp_le_exp.mpr (hUlow _)
    have hval : (∫ _z : ℝ, Real.exp (-M) ∂gaussianReal 0 1) = Real.exp (-M) := by simp
    rw [hval] at hle
    exact lt_of_lt_of_le (Real.exp_pos _) hle
  set G : ℝ → ℝ := fun z => Real.exp (U (x + Real.sqrt s * z)) with hG
  have hGint' : Integrable G (gaussianReal 0 1) := hGint
  have hpoint : ∀ z, U (x + Real.sqrt s * z) ≤ Real.log A + (G z - A) / A := by
    intro z
    have hGpos : 0 < G z := Real.exp_pos _
    have hlogG : Real.log (G z) = U (x + Real.sqrt s * z) := by simp [hG]
    have := Real.log_le_sub_one_of_pos (div_pos hGpos hApos)
    rw [Real.log_div (ne_of_gt hGpos) (ne_of_gt hApos), hlogG] at this
    have h2 : G z / A - 1 = (G z - A) / A := by field_simp
    linarith [this, h2.le, h2.ge]
  have hright_int : Integrable (fun z : ℝ => Real.log A + (G z - A) / A) (gaussianReal 0 1) := by
    have h1 : Integrable (fun z : ℝ => (G z - A) / A) (gaussianReal 0 1) :=
      ((hGint'.sub (integrable_const A))).div_const A
    exact (integrable_const (Real.log A)).add h1
  have hmono := integral_mono hUint hright_int hpoint
  have hright_val : ∫ z, (Real.log A + (G z - A) / A) ∂gaussianReal 0 1 = Real.log A := by
    have h1 : Integrable (fun z : ℝ => (G z - A) / A) (gaussianReal 0 1) :=
      ((hGint'.sub (integrable_const A))).div_const A
    rw [integral_add (integrable_const (Real.log A)) h1]
    have h2 : ∫ z, (G z - A) / A ∂gaussianReal 0 1 = 0 := by
      rw [integral_div]
      rw [integral_sub hGint' (integrable_const A)]
      have hGA : (∫ z, G z ∂gaussianReal 0 1) = A := by rw [hA]
      rw [hGA]
      simp
    rw [h2]
    simp
  rw [hright_val] at hmono
  simpa [hA] using hmono
lemma gaussianTransform_step_upper {s d w M : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U) (hUlow : ∀ x, -M ≤ U x)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) - w / 2) (hwM : -w / 2 ≤ M) (x : ℝ) :
    gaussianTransform s d U x ≤ Real.log (Real.cosh x) + s / 2 - w / 2 := by
  by_cases hd0 : d = 0
  · simp only [gaussianTransform, hd0, ite_true]
    have hstep := integral_le_log_integral_exp (s := s) (w := w) (M := M)
      hUmeas hUlow hUup hwM x
    have hGint := integrable_exp_shift_of_bounds (s := s) (w := w) (M := M)
      hUmeas hUlow hUup x
    have hbound_int : Integrable (fun z : ℝ =>
        Real.cosh (x + Real.sqrt s * z) * Real.exp (-(w / 2))) (gaussianReal 0 1) :=
      (integrable_cosh_gaussianReal x s).mul_const _
    have hpoint : ∀ z : ℝ, Real.exp (U (x + Real.sqrt s * z))
        ≤ Real.cosh (x + Real.sqrt s * z) * Real.exp (-(w / 2)) := by
      intro z
      have := exp_mul_le_cosh_rpow (d := 1) zero_le_one hUup (x + Real.sqrt s * z)
      simpa using this
    have hA_le : (∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)
        ≤ Real.cosh x * Real.exp (s / 2) * Real.exp (-(w / 2)) := by
      calc ∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1
          ≤ ∫ z, Real.cosh (x + Real.sqrt s * z) * Real.exp (-(w / 2))
              ∂gaussianReal 0 1 := integral_mono hGint hbound_int hpoint
        _ = (∫ z, Real.cosh (x + Real.sqrt s * z) ∂gaussianReal 0 1)
              * Real.exp (-(w / 2)) := integral_mul_const _ _
        _ = Real.cosh x * Real.exp (s / 2) * Real.exp (-(w / 2)) := by
            rw [integral_cosh_gaussianReal hs x]
    have hApos : 0 < ∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
      have hconst : Integrable (fun _ : ℝ => Real.exp (-M)) (gaussianReal 0 1) :=
        integrable_const _
      have hle : (∫ _z : ℝ, Real.exp (-M) ∂gaussianReal 0 1)
          ≤ ∫ z, Real.exp (U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
        apply integral_mono hconst hGint
        intro z; exact Real.exp_le_exp.mpr (hUlow _)
      have hval : (∫ _z : ℝ, Real.exp (-M) ∂gaussianReal 0 1) = Real.exp (-M) := by simp
      rw [hval] at hle
      exact lt_of_lt_of_le (Real.exp_pos _) hle
    have hlog_le := Real.log_le_log hApos hA_le
    rw [Real.log_mul (mul_pos (Real.cosh_pos x) (Real.exp_pos (s / 2))).ne'
        (Real.exp_pos (-(w / 2))).ne',
      Real.log_mul (Real.cosh_pos x).ne' (Real.exp_pos (s / 2)).ne',
      Real.log_exp, Real.log_exp] at hlog_le
    linarith
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    simp only [gaussianTransform, hd0, ite_false]
    have hJ := jensen_step_pos (M := M) hs hdpos hd1 hUmeas hUlow hUup x
    have hpos_low : 0 < Real.exp (-(d * M)) := Real.exp_pos _
    have hconst : Integrable (fun _ : ℝ => Real.exp (-(d * M))) (gaussianReal 0 1) :=
      integrable_const _
    have hGint := integrable_exp_mul_u_gaussianReal (M := M) hs hd hd1 hUmeas hUup x
    have hle : Real.exp (-(d * M))
        ≤ ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
      calc Real.exp (-(d * M)) = ∫ _z : ℝ, Real.exp (-(d * M)) ∂gaussianReal 0 1 := by simp
        _ ≤ ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
            integral_mono hconst hGint (fun z => Real.exp_le_exp.mpr (by
              have := hUlow (x + Real.sqrt s * z); nlinarith))
    have hIpos : 0 < ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
      lt_of_lt_of_le hpos_low hle
    have hlog_le : Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)
        ≤ Real.log ((Real.cosh x) ^ d * Real.exp (s * d / 2 - d * w / 2)) :=
      Real.log_le_log hIpos hJ
    rw [Real.log_mul (Real.rpow_pos_of_pos (Real.cosh_pos x) d).ne'
      (Real.exp_pos (s * d / 2 - d * w / 2)).ne',
      Real.log_rpow (Real.cosh_pos x), Real.log_exp] at hlog_le
    rw [div_le_iff₀ hdpos]
    nlinarith
lemma gaussianTransform_step_lower {s d w M : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U) (hUlow : ∀ x, -M ≤ U x)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) - w / 2) (hwM : -w / 2 ≤ M) (x : ℝ) :
    -M ≤ gaussianTransform s d U x := by
  by_cases hd0 : d = 0
  · simp only [gaussianTransform, hd0, ite_true]
    have hUint := integrable_shift_of_bounds (s := s) (w := w) (M := M)
      hUmeas hUlow hUup hwM x
    have hconst : Integrable (fun _ : ℝ => -M) (gaussianReal 0 1) := integrable_const _
    have := integral_mono hconst hUint (fun z => hUlow _)
    simpa using this
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    simp only [gaussianTransform, hd0, ite_false]
    have hGint := integrable_exp_mul_u_gaussianReal (M := M) hs hd hd1 hUmeas hUup x
    have hconst : Integrable (fun _ : ℝ => Real.exp (-(d * M))) (gaussianReal 0 1) :=
      integrable_const _
    have hle : Real.exp (-(d * M))
        ≤ ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 := by
      calc Real.exp (-(d * M)) = ∫ _z : ℝ, Real.exp (-(d * M)) ∂gaussianReal 0 1 := by simp
        _ ≤ ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
            integral_mono hconst hGint (fun z => Real.exp_le_exp.mpr (by
              have := hUlow (x + Real.sqrt s * z); nlinarith))
    have hIpos : 0 < ∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1 :=
      lt_of_lt_of_le (Real.exp_pos _) hle
    have hlog : -(d * M) ≤
        Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) := by
      calc -(d * M) = Real.log (Real.exp (-(d * M))) := by rw [Real.log_exp]
        _ ≤ Real.log (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1) :=
            Real.log_le_log (Real.exp_pos _) hle
    rw [le_div_iff₀ hdpos]
    nlinarith
lemma measurable_integral_shift {s : ℝ} {U : ℝ → ℝ} (hU : Measurable U) :
    Measurable (fun x : ℝ => ∫ z, U (x + Real.sqrt s * z) ∂gaussianReal 0 1) := by
  have hun : StronglyMeasurable
      (Function.uncurry fun x z : ℝ => U (x + Real.sqrt s * z)) := by
    apply hU.stronglyMeasurable.comp_measurable
    fun_prop
  exact (hun.integral_prod_right (ν := gaussianReal 0 1)).measurable
lemma measurable_log_integral_shift {s d : ℝ} {U : ℝ → ℝ} (hU : Measurable U) :
    Measurable (fun x : ℝ => Real.log
      (∫ z, Real.exp (d * U (x + Real.sqrt s * z)) ∂gaussianReal 0 1)) := by
  have hun : StronglyMeasurable
      (Function.uncurry fun x z : ℝ => Real.exp (d * U (x + Real.sqrt s * z))) := by
    apply (Real.measurable_exp.comp (hU.const_mul d)).stronglyMeasurable.comp_measurable
    fun_prop
  exact ((hun.integral_prod_right (ν := gaussianReal 0 1)).measurable.log)
lemma gaussianTransform_measurable {s d : ℝ} {U : ℝ → ℝ} (hU : Measurable U) :
    Measurable (gaussianTransform s d U) := by
  unfold gaussianTransform
  by_cases hd : d = 0
  · simp only [if_pos hd]
    exact measurable_integral_shift hU
  · simp only [if_neg hd]
    exact (measurable_log_integral_shift (d := d) hU).div_const d
lemma gaussianTransform_step_upper' {s d c M : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U) (hUlow : ∀ x, -M ≤ U x)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) + c) (hcM : c ≤ M) (x : ℝ) :
    gaussianTransform s d U x ≤ Real.log (Real.cosh x) + s / 2 + c := by
  have h := gaussianTransform_step_upper (w := -2 * c) hs hd hd1 hUmeas hUlow
    (fun y => by have := hUup y; linarith) (by linarith) x
  calc gaussianTransform s d U x
      ≤ Real.log (Real.cosh x) + s / 2 - (-2 * c) / 2 := h
    _ = Real.log (Real.cosh x) + s / 2 + c := by ring
lemma gaussianTransform_step_lower' {s d c M : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    {U : ℝ → ℝ} (hUmeas : Measurable U) (hUlow : ∀ x, -M ≤ U x)
    (hUup : ∀ x, U x ≤ Real.log (Real.cosh x) + c) (hcM : c ≤ M) (x : ℝ) :
    -M ≤ gaussianTransform s d U x := by
  exact gaussianTransform_step_lower (w := -2 * c) hs hd hd1 hUmeas hUlow
    (fun y => by have := hUup y; linarith) (by linarith) x
lemma fold_gaussianTransform_bounds (L : List (ℝ × ℝ)) (M c : ℝ)
    (hL : ∀ p ∈ L, 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hcM : c + (L.map Prod.fst).sum / 2 ≤ M)
    {V : ℝ → ℝ} (hVmeas : Measurable V) (hVlow : ∀ x, -M ≤ V x)
    (hVup : ∀ x, V x ≤ Real.log (Real.cosh x) + c) :
    (∀ x, L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V x
        ≤ Real.log (Real.cosh x) + c + (L.map Prod.fst).sum / 2) ∧
    (∀ x, -M ≤ L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V x) ∧
    Measurable (L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V) := by
  induction L with
  | nil =>
      refine ⟨fun x => ?_, hVlow, hVmeas⟩
      simpa using hVup x
  | cons a L ih =>
      obtain ⟨ha1, ha2, ha3⟩ := hL a (by simp)
      have htail : ∀ p ∈ L, 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := fun p hp =>
        hL p (by simp [hp])
      have hsum : ((a :: L).map Prod.fst).sum = a.1 + (L.map Prod.fst).sum := by simp
      rw [hsum] at hcM
      have hcM' : c + (L.map Prod.fst).sum / 2 ≤ M := by linarith
      have hih := ih htail hcM'
      set W : ℝ → ℝ := L.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V with hW
      have hWmeas : Measurable W := hih.2.2
      have hWlow : ∀ x, -M ≤ W x := hih.2.1
      have hWup : ∀ x, W x ≤ Real.log (Real.cosh x) + (c + (L.map Prod.fst).sum / 2) := by
        intro x
        have := hih.1 x
        linarith
      have hcM'' : c + (L.map Prod.fst).sum / 2 ≤ M := hcM'
      have hstep_up : ∀ x, gaussianTransform a.1 a.2 W x
          ≤ Real.log (Real.cosh x) + a.1 / 2 + (c + (L.map Prod.fst).sum / 2) := fun x =>
        gaussianTransform_step_upper' ha1 ha2 ha3 hWmeas hWlow hWup hcM'' x
      have hstep_low : ∀ x, -M ≤ gaussianTransform a.1 a.2 W x := fun x =>
        gaussianTransform_step_lower' ha1 ha2 ha3 hWmeas hWlow hWup hcM'' x
      have hstep_meas : Measurable (gaussianTransform a.1 a.2 W) :=
        gaussianTransform_measurable hWmeas
      have hfold : (a :: L).foldr (fun sd U => gaussianTransform sd.1 sd.2 U) V
          = gaussianTransform a.1 a.2 W := by
        simp [hW]
      refine ⟨?_, ?_, ?_⟩
      · intro x
        rw [hfold, hsum]
        have := hstep_up x
        calc gaussianTransform a.1 a.2 W x
            ≤ Real.log (Real.cosh x) + a.1 / 2 + (c + (L.map Prod.fst).sum / 2) := this
          _ = Real.log (Real.cosh x) + c + (a.1 + (L.map Prod.fst).sum) / 2 := by ring
      · intro x
        rw [hfold]
        exact hstep_low x
      · rw [hfold]
        exact hstep_meas
lemma stepAt_nonneg (h : FieldStep) (i : ℕ) : 0 ≤ stepAt h i := by
  unfold stepAt
  split_ifs with hi
  · exact h.nonneg _
  · exact le_refl 0
lemma stepAt_mono_of_lt (h : FieldStep) {i j : ℕ} (hij : i ≤ j)
    (hj : j < h.partition.levels) : stepAt h i ≤ stepAt h j := by
  have hi : i < h.partition.levels := lt_of_le_of_lt hij hj
  have h1 : stepAt h i = h.value ⟨i, hi⟩ := by simp [stepAt, hi]
  have h2 : stepAt h j = h.value ⟨j, hj⟩ := by simp [stepAt, hj]
  rw [h1, h2]
  exact h.ordered (Fin.mk_le_mk.mpr hij)
lemma cut_nonneg (h : FieldStep) (i : Fin (h.partition.levels + 1)) :
    0 ≤ h.partition.cut i := by
  have hmono : Monotone h.partition.cut := h.partition.ordered.monotone
  have h0 : (⟨0, Nat.zero_lt_succ h.partition.levels⟩ : Fin (h.partition.levels + 1)) ≤ i :=
    Fin.zero_le i
  have := hmono h0
  rwa [h.partition.first] at this
lemma cut_le_one (h : FieldStep) (i : Fin (h.partition.levels + 1)) :
    h.partition.cut i ≤ 1 := by
  have hmono : Monotone h.partition.cut := h.partition.ordered.monotone
  have hlast : i ≤ (⟨h.partition.levels, Nat.lt_succ_self h.partition.levels⟩ :
      Fin (h.partition.levels + 1)) := Fin.le_last i
  have := hmono hlast
  rwa [h.partition.last] at this
lemma stepAt_increment_nonneg (h : FieldStep) {i : ℕ} (hi : i < h.partition.levels) :
    0 ≤ stepAt h i - (if i = 0 then 0 else stepAt h (i - 1)) := by
  by_cases h0 : i = 0
  · have hzi : stepAt h i = stepAt h 0 := by rw [h0]
    rw [h0, if_pos rfl]
    simp only [sub_zero]
    exact stepAt_nonneg h 0
  · have hle : i - 1 ≤ i := Nat.sub_le i 1
    have hmono := stepAt_mono_of_lt h hle hi
    rw [if_neg h0]
    linarith
lemma sum_increments_eq (h : FieldStep) :
    ((List.ofFn (fun i : Fin h.partition.levels =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc))).map Prod.fst).sum
      = stepAt h (h.partition.levels - 1) := by
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => stepAt h i - (if i = 0 then 0 else stepAt h (i - 1))) h.partition.levels]
  have htel := Finset.sum_range_sub
    (fun i : ℕ => if i = 0 then (0:ℝ) else stepAt h (i - 1)) h.partition.levels
  have hterm : ∀ i ∈ Finset.range h.partition.levels,
      stepAt h i - (if i = 0 then 0 else stepAt h (i - 1))
        = (if i + 1 = 0 then (0:ℝ) else stepAt h (i + 1 - 1))
          - (if i = 0 then 0 else stepAt h (i - 1)) := by
    intro i hi
    have : i + 1 ≠ 0 := Nat.succ_ne_zero i
    rw [if_neg this, Nat.succ_sub_one]
  rw [Finset.sum_congr rfl hterm, htel]
  have h0 : (if (0:ℕ) = 0 then (0:ℝ) else stepAt h (0 - 1)) = 0 := if_pos rfl
  rw [h0, sub_zero]
  have hk : h.partition.levels ≠ 0 := Nat.pos_iff_ne_zero.mp h.partition.positive
  rw [if_neg hk]
lemma increments_mem (h : FieldStep) :
    ∀ p ∈ List.ofFn (fun i : Fin h.partition.levels =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc)), 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := by
  intro p hp
  rw [List.mem_ofFn] at hp
  obtain ⟨i, rfl⟩ := hp
  exact ⟨stepAt_increment_nonneg h i.isLt,
    cut_nonneg h i.castSucc, cut_le_one h i.castSucc⟩
theorem fieldRecursion_le_zero (h : FieldStep) : fieldRecursion h ≤ 0 := by
  set k := h.partition.levels with hk
  set W := stepAt h (k - 1) with hW
  have hWnonneg : 0 ≤ W := stepAt_nonneg h (k - 1)
  have hincr := increments_mem h
  have hsum : ((List.ofFn (fun i : Fin k =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc))).map Prod.fst).sum = W := by
    rw [hW]
    exact sum_increments_eq h
  have hVmeas : Measurable (fun x : ℝ => Real.log (Real.cosh x) - W / 2) := by fun_prop
  have hVlow : ∀ x, -(W / 2) ≤ Real.log (Real.cosh x) - W / 2 := by
    intro x
    have h1 : (1:ℝ) ≤ Real.cosh x := Real.one_le_cosh x
    have := Real.log_nonneg h1
    linarith
  have hVup : ∀ x, Real.log (Real.cosh x) - W / 2
      ≤ Real.log (Real.cosh x) + (-(W / 2)) := fun x => le_refl _
  have hcM : (-(W / 2)) + ((List.ofFn (fun i : Fin k =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc))).map Prod.fst).sum / 2 ≤ W / 2 := by
    rw [hsum]; linarith
  have hfold := fold_gaussianTransform_bounds
    (List.ofFn (fun i : Fin k =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc))) (W / 2) (-(W / 2)) hincr hcM hVmeas hVlow hVup
  have hmain : (List.ofFn (fun i : Fin k =>
      (stepAt h i - (if i.val = 0 then 0 else stepAt h (i.val - 1)),
        h.partition.cut i.castSucc))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U)
        (fun x => Real.log (Real.cosh x) - W / 2) 0 ≤ 0 := by
    have h1 := hfold.1 0
    rw [hsum] at h1
    have hc : Real.log (Real.cosh (0:ℝ)) = 0 := by simp
    rw [hc] at h1
    linarith
  simpa [fieldRecursion, hk] using hmain
def zeroPath : OverlapPath where
  val := AEEqFun.const ℝ (0 : ℝ)
  admissible := ⟨fun _ => 0, (AEEqFun.coeFn_const (α := ℝ) (μ := pathMeasure) (β := ℝ) 0).symm, by
    intro a b ha hb hab; exact le_refl 0, by
    intro u hu; exact ⟨le_refl 0, zero_le_one⟩⟩
lemma stepFunction_measurable (h : FieldStep) : Measurable (stepFunction h) := by
  unfold stepFunction
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  · exact measurable_const
  · exact measurable_const
lemma zeroPath_integral (h : FieldStep) :
    ∫ u, stepFunction h u * zeroPath.val u ∂pathMeasure = 0 := by
  have hzero : (zeroPath.val : ℝ → ℝ) =ᵐ[pathMeasure] Function.const ℝ (0:ℝ) := by
    simpa [zeroPath] using
      (AEEqFun.coeFn_const (α := ℝ) (μ := pathMeasure) (β := ℝ) (0:ℝ))
  have : (fun u => stepFunction h u * zeroPath.val u) =ᵐ[pathMeasure] (fun _ => (0:ℝ)) := by
    filter_upwards [hzero] with u hu
    simp [hu]
  rw [integral_congr_ae this]
  simp
lemma isingEntropy_zeroPath_le_zero : isingEntropy zeroPath ≤ 0 := by
  unfold isingEntropy
  refine iSup_le ?_
  intro h
  rw [zeroPath_integral h]
  have := fieldRecursion_le_zero h
  simpa using (EReal.coe_le_coe_iff.mpr this :
    ((fieldRecursion h : ℝ) : EReal) ≤ (0 : EReal))
lemma limUnder_bounds {u : ℕ → ℝ} {K : ℝ} (h : ∀ n, |u n| ≤ K) :
    min (-K) (Classical.choice (inferInstance : Nonempty ℝ)) ≤ Filter.limUnder atTop u ∧
    Filter.limUnder atTop u ≤ max K (Classical.choice (inferInstance : Nonempty ℝ)) := by
  by_cases hconv : ∃ x : ℝ, Tendsto u atTop (𝓝 x)
  · obtain ⟨x, hx⟩ := hconv
    have hlim : Filter.limUnder atTop u = x := hx.limUnder_eq
    rw [hlim]
    constructor
    · apply le_trans (min_le_left _ _)
      exact ge_of_tendsto hx (Filter.Eventually.of_forall (fun n => (abs_le.mp (h n)).1))
    · apply le_trans (le_of_tendsto hx (Filter.Eventually.of_forall (fun n => (abs_le.mp (h n)).2)))
      exact le_max_left _ _
  · have hlim : Filter.limUnder atTop u
        = Classical.choice (inferInstance : Nonempty ℝ) := limUnder_of_not_tendsto hconv
    rw [hlim]
    exact ⟨min_le_right _ _, le_max_right _ _⟩
lemma ereal_iInf_eq_coe_of_bounds {ι : Type*} (f : ι → EReal) (i0 : ι) {a b : ℝ}
    (ha : ∀ i, (a : EReal) ≤ f i) (hb : f i0 ≤ (b : EReal)) :
    ∃ p : ℝ, (⨅ i, f i) = (p : EReal) := by
  have hle : (a : EReal) ≤ ⨅ i, f i := le_iInf ha
  have hge : (⨅ i, f i) ≤ (b : EReal) := (iInf_le f i0).trans hb
  have hne_bot : (⨅ i, f i) ≠ ⊥ := by
    intro h
    rw [h] at hle
    exact EReal.coe_ne_bot a (le_bot_iff.mp hle)
  have hne_top : (⨅ i, f i) ≠ ⊤ := by
    intro h
    rw [h] at hge
    exact absurd hge (not_le.mpr (EReal.coe_lt_top b))
  exact ⟨(⨅ i, f i).toReal, (EReal.coe_toReal hne_top hne_bot).symm⟩
theorem variationalValue_real_of_continuous {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) (hbounded : ∃ K : ℝ, ∀ x, |f x| ≤ K) :
    ∃ p : ℝ, variationalValue α f = (p : EReal) := by
  obtain ⟨K, hK⟩ := hbounded
  let c : ℝ := Classical.choice (inferInstance : Nonempty ℝ)
  have hlow : ∀ q : OverlapPath,
      ((α * min (-K) c : ℝ) : EReal) ≤ (α * patternFunctional f q : ℝ) + isingEntropy q := by
    intro q
    have hpt : ∀ n : ℕ, |uniformPattern f q n| ≤ K := uniformPattern_abs_le f K hf hK q
    have hb : min (-K) c ≤ patternFunctional f q := (limUnder_bounds hpt).1
    have hmul : α * min (-K) c ≤ α * patternFunctional f q :=
      mul_le_mul_of_nonneg_left hb hα
    have hcoe : ((α * min (-K) c : ℝ) : EReal) ≤ ((α * patternFunctional f q : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hmul
    calc ((α * min (-K) c : ℝ) : EReal)
        ≤ ((α * patternFunctional f q : ℝ) : EReal) := hcoe
      _ ≤ (α * patternFunctional f q : ℝ) + isingEntropy q :=
          le_add_of_nonneg_right (isingEntropy_nonneg q)
  have hup : ((α * patternFunctional f zeroPath : ℝ) : EReal) + isingEntropy zeroPath
      ≤ ((α * max K c : ℝ) : EReal) := by
    have hpt : ∀ n : ℕ, |uniformPattern f zeroPath n| ≤ K :=
      uniformPattern_abs_le f K hf hK zeroPath
    have hb : patternFunctional f zeroPath ≤ max K c := (limUnder_bounds hpt).2
    have hmul : α * patternFunctional f zeroPath ≤ α * max K c :=
      mul_le_mul_of_nonneg_left hb hα
    have hcoe : ((α * patternFunctional f zeroPath : ℝ) : EReal) ≤ ((α * max K c : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr hmul
    calc ((α * patternFunctional f zeroPath : ℝ) : EReal) + isingEntropy zeroPath
        ≤ ((α * patternFunctional f zeroPath : ℝ) : EReal) + 0 :=
          add_le_add_right isingEntropy_zeroPath_le_zero _
      _ = ((α * patternFunctional f zeroPath : ℝ) : EReal) := add_zero _
      _ ≤ ((α * max K c : ℝ) : EReal) := hcoe
  have hmain := ereal_iInf_eq_coe_of_bounds
    (fun q : OverlapPath => (α * patternFunctional f q : ℝ) + isingEntropy q) zeroPath hlow hup
  simpa [variationalValue] using hmain
end IsingPerceptron
end

end OAI
