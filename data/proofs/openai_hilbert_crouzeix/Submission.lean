import Mathlib

namespace OAI

noncomputable section

open Complex Set
open scoped TensorProduct Matrix.Norms.L2Operator Classical ComplexConjugate

namespace HilbertCrouzeix

universe u

abbrev Coeff (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
abbrev CoeffSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def numericalRange (A : H →L[ℂ] H) : Set ℂ :=
  {z | ∃ x : H, ‖x‖ = 1 ∧ inner ℂ x (A x) = z}

def numericalClosure (A : H →L[ℂ] H) : Set ℂ := closure (numericalRange A)

abbrev Amplification (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℕ) := UniformSpace.Completion (H ⊗[ℂ] CoeffSpace m)

def tensorOp {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  (TensorProduct.mapL A (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B)).completion

def matrixPolynomial {m d : ℕ} (B : Fin (d + 1) → Coeff m) (z : ℂ) : Coeff m :=
  ∑ k : Fin (d + 1), z ^ k.val • B k

def polynomialEval {m d : ℕ} (A : H →L[ℂ] H) (B : Fin (d + 1) → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ k : Fin (d + 1), tensorOp (A ^ k.val) (B k)

def normSup {E : Type*} [Norm E] (S : Set ℂ) (f : ℂ → E) : ℝ :=
  if S.Nonempty then sSup ((fun z => ‖f z‖) '' S) else 0
def contourIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : ℝ → ℂ) (f : ℂ → E) : E :=
  ∫ t : ℝ in (0 : ℝ)..1, deriv γ t • f (γ t)

def contourIndex (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * contourIntegral γ (fun w => (w - z)⁻¹)

def IsCauchyContour (K U : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ContDiff ℝ 1 γ ∧ γ 0 = γ 1 ∧
  (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U \ K) ∧
  (∀ z ∈ K, contourIndex γ z = 1) ∧
  (∀ z ∉ U, contourIndex γ z = 0)

def chosenContour (K U : Set ℂ) : ℝ → ℂ :=
  Classical.epsilon (IsCauchyContour K U)

variable [CompleteSpace H]

def dunfordIntegral (A : H →L[ℂ] H) (γ : ℝ → ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ •
    contourIntegral γ (fun z => f z • resolvent A z)

def holomorphicCalculus (A : H →L[ℂ] H) (U : Set ℂ) (f : ℂ → ℂ) : H →L[ℂ] H :=
  dunfordIntegral A (chosenContour (numericalClosure A) U) f

def matrixUnit {m : ℕ} (i j : Fin m) : Coeff m := Matrix.single i j 1

def holomorphicEval {m : ℕ} (A : H →L[ℂ] H) (U : Set ℂ) (F : ℂ → Coeff m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m,
    tensorOp (holomorphicCalculus A U (fun z => F z i j)) (matrixUnit i j)
abbrev RationalMatrix (m : ℕ) := Matrix (Fin m) (Fin m) (RatFunc ℂ)

def poleFreeSet {m : ℕ} (R : RationalMatrix m) : Set ℂ :=
  {z | ∀ i j, (R i j).denom.eval z ≠ 0}

def rationalFunction {m : ℕ} (R : RationalMatrix m) (z : ℂ) : Coeff m :=
  fun i j => RatFunc.eval (RingHom.id ℂ) z (R i j)

def rationalCalculus (A : H →L[ℂ] H) (r : RatFunc ℂ) : H →L[ℂ] H :=
  Polynomial.aeval A r.num * Ring.inverse (Polynomial.aeval A r.denom)

def rationalEval {m : ℕ} (A : H →L[ℂ] H) (R : RationalMatrix m) :
    Amplification H m →L[ℂ] Amplification H m :=
  ∑ i : Fin m, ∑ j : Fin m, tensorOp (rationalCalculus A (R i j)) (matrixUnit i j)
def ZeroConclusion (A : H →L[ℂ] H) : Prop :=
  numericalRange A = ∅ ∧
  (∀ (m : ℕ) (F : ℂ → Coeff m), normSup (numericalRange A) F = 0) ∧
  ∀ (m : ℕ), 0 < m →
    (∀ T : Amplification H m →L[ℂ] Amplification H m, T = 0) ∧
    (∀ (d : ℕ) (B : Fin (d + 1) → Coeff m), polynomialEval A B = 0 ∧
      ‖polynomialEval A B‖ ≤ 2 * normSup (numericalRange A) (matrixPolynomial B)) ∧
    (∀ (U : Set ℂ) (F : ℂ → Coeff m), holomorphicEval A U F = 0 ∧
      ‖holomorphicEval A U F‖ ≤ 2 * normSup (numericalRange A) F) ∧
    (∀ (R : RationalMatrix m), rationalEval A R = 0 ∧
      ‖rationalEval A R‖ ≤ 2 * normSup (numericalRange A) (rationalFunction R))

section CompressionDefinitions
omit [CompleteSpace H]

def compression (A : H →L[ℂ] H) (E : Submodule ℂ H) [E.HasOrthogonalProjection] :
    E →L[ℂ] E := E.orthogonalProjectionOnto.comp (A.comp E.subtypeL)
def completedIsometry {V : Type*} {W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedSpace ℂ V] [NormedSpace ℂ W]
    (f : V →ₗᵢ[ℂ] W) : UniformSpace.Completion V →ₗᵢ[ℂ] UniformSpace.Completion W :=
  { f.toContinuousLinearMap.completion.toLinearMap with
    norm_map' := f.isometry.completion_map.norm_map_of_map_zero
      (f.toContinuousLinearMap.completion.map_zero) }

def tensorInclusion (E : Submodule ℂ H) (m : ℕ) :
    Amplification E m →ₗᵢ[ℂ] Amplification H m :=
  completedIsometry (TensorProduct.mapIsometry E.subtypeₗᵢ (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m))

lemma numericalClosure_isCompact (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) := by
  have hsub : numericalClosure A ⊆ Metric.closedBall (0 : ℂ) ‖A‖ := by
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro z ⟨x, hx, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖inner ℂ x (A x)‖ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm x (A x)
      _ ≤ 1 * (‖A‖ * ‖x‖) := by
        exact mul_le_mul hx.le (A.le_opNorm x) (norm_nonneg _) zero_le_one
      _ = ‖A‖ := by rw [hx]; ring
  exact (isCompact_closedBall (0 : ℂ) ‖A‖).of_isClosed_subset
    isClosed_closure hsub
lemma tensorOp_tmul {m : ℕ} (A : H →L[ℂ] H) (B : Coeff m) (x : H) (f : CoeffSpace m) :
    tensorOp A B (↑(x ⊗ₜ[ℂ] f) : Amplification H m) =
      (↑(A x ⊗ₜ[ℂ]
        (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B) f) :
        Amplification H m) := by
  rw [tensorOp, ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
end CompressionDefinitions

lemma tensorInclusion_coe {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) (m : ℕ) (v : E ⊗[ℂ] CoeffSpace m) :
    tensorInclusion E m (↑v : Amplification E m) =
      (↑(TensorProduct.mapIsometry E.subtypeₗᵢ
        (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m) v) : Amplification H m) := by
  rw [tensorInclusion]
  change (TensorProduct.mapIsometry E.subtypeₗᵢ
      (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m)).toContinuousLinearMap.completion
      (↑v : UniformSpace.Completion (E ⊗[ℂ] CoeffSpace m)) =
    (↑((TensorProduct.mapIsometry E.subtypeₗᵢ
      (.id : CoeffSpace m →ₗᵢ[ℂ] CoeffSpace m)) v) :
      UniformSpace.Completion (H ⊗[ℂ] CoeffSpace m))
  rw [ContinuousLinearMap.completion_apply_coe,
    LinearIsometry.coe_toContinuousLinearMap]
lemma numericalRange_eq_empty_of_subsingleton {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Subsingleton H]
    (A : H →L[ℂ] H) : numericalRange A = ∅ := by
  ext z
  constructor
  · rintro ⟨x, hx, -⟩
    rw [Subsingleton.elim x 0, norm_zero] at hx
    norm_num at hx
  · intro h
    exact h.elim
lemma normSup_empty {E : Type*} [Norm E] (f : ℂ → E) :
    normSup (∅ : Set ℂ) f = 0 := by
  simp [normSup]
lemma subsingleton_completion_of_subsingleton {α : Type*} [UniformSpace α]
    [Subsingleton α] : Subsingleton (UniformSpace.Completion α) := by
  constructor
  intro a b
  exact UniformSpace.Completion.induction_on₂ a b
    (isClosed_eq (f := Prod.fst) (g := Prod.snd) continuous_fst continuous_snd)
    (fun x y => congrArg (fun z : α => (↑z : UniformSpace.Completion α))
      (Subsingleton.elim x y))
lemma subsingleton_amplification {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Subsingleton H] (m : ℕ) :
    Subsingleton (Amplification H m) := by
  haveI : Subsingleton (H ⊗[ℂ] CoeffSpace m) := inferInstance
  exact subsingleton_completion_of_subsingleton (α := H ⊗[ℂ] CoeffSpace m)
lemma realLinear_exists_unit_norm_add_kernel
    (k : EuclideanSpace ℝ (Fin 3)) (hk0 : k ≠ 0)
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ ≤ 1) :
    ∃ t : ℝ, ‖n + t • k‖ = 1 := by
  by_cases h1 : ‖n‖ = 1
  · exact ⟨0, by simpa using h1⟩
  · have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk0
    let R : ℝ := (‖n‖ + 1) / ‖k‖
    have hR0 : 0 ≤ R := by
      dsimp [R]
      positivity
    have hcont : ContinuousOn (fun t : ℝ => ‖n + t • k‖) (Icc 0 R) := by
      fun_prop
    have hg0 : ‖n + (0 : ℝ) • k‖ = ‖n‖ := by simp
    have hge : 1 ≤ ‖n + R • k‖ := by
      have htri := norm_sub_norm_le (R • k) (-n)
      have hnorm : ‖R • k‖ = R * ‖k‖ := by
        rw [norm_smul, Real.norm_of_nonneg hR0]
      have hnorm' : ‖(R • k : EuclideanSpace ℝ (Fin 3)) - (-n)‖ =
          ‖n + R • k‖ := by
        rw [sub_neg_eq_add, add_comm]
      have hRk : R * ‖k‖ = ‖n‖ + 1 := by
        dsimp [R]
        field_simp [hkpos.ne']
      rw [norm_neg, hnorm, hRk] at htri
      rw [hnorm'] at htri
      linarith
    have hmem : (1 : ℝ) ∈ Icc (‖n + (0 : ℝ) • k‖) (‖n + R • k‖) :=
      ⟨by simpa [hg0] using hn, hge⟩
    obtain ⟨t, _ht, hgt⟩ := intermediate_value_Icc hR0 hcont hmem
    exact ⟨t, hgt⟩
lemma spectrum_subset_numericalClosure (A : H →L[ℂ] H) :
    spectrum ℂ A ⊆ numericalClosure A := by
  intro z hz
  by_contra hznot
  haveI : Nontrivial H := by
    by_contra hnt
    have hsub : Subsingleton H := not_nontrivial_iff_subsingleton.mp hnt
    have hsubL : Subsingleton (H →L[ℂ] H) :=
      ⟨fun f g => ContinuousLinearMap.ext fun x => hsub.elim _ _⟩
    have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) z - A) := by
      rw [hsubL.elim (algebraMap ℂ (H →L[ℂ] H) z - A) 1]
      exact isUnit_one
    exact (spectrum.mem_iff.mp hz) hunit
  have hne : (numericalRange A).Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    exact ⟨inner ℂ ((‖x‖⁻¹ : ℂ) • x) (A ((‖x‖⁻¹ : ℂ) • x)),
      (‖x‖⁻¹ : ℂ) • x, norm_smul_inv_norm hx, rfl⟩
  have hε : 0 < Metric.infDist z (numericalRange A) :=
    (Metric.infDist_pos_iff_notMem_closure hne).mp hznot
  set ε : NNReal := ⟨Metric.infDist z (numericalRange A), le_of_lt hε⟩ with hεdef
  set g : H →L[ℂ] H := algebraMap ℂ (H →L[ℂ] H) z - A with hgdef
  have hinner_g : ∀ x : H, inner ℂ x (g x) = z * inner ℂ x x - inner ℂ x (A x) := by
    intro x
    rw [hgdef, sub_apply, Algebra.algebraMap_eq_smul_one,
      smul_apply, one_apply_eq_self, inner_sub_right,
      inner_smul_right]
  have key : ∀ x : H, ‖x‖ ^ 2 * (ε : ℝ) ≤ ‖inner ℂ (g x) x‖ := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    · let u : H := ((‖x‖ : ℂ))⁻¹ • x
      have hu : ‖u‖ = 1 := by
        simpa [u] using norm_smul_inv_norm (𝕜 := ℂ) hx
      have hxne : (‖x‖ : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hx
      have hxrepr : (‖x‖ : ℂ) • u = x := by
        simpa only [u, smul_smul] using smul_inv_smul₀ hxne x
      have hinneru : inner ℂ u (g u) = z - inner ℂ u (A u) := by
        rw [hinner_g u, inner_self_eq_norm_sq_to_K, hu]
        norm_num
      have hle : (ε : ℝ) ≤ ‖inner ℂ u (g u)‖ := by
        have hle0 : Metric.infDist z (numericalRange A) ≤
            dist z (inner ℂ u (A u)) :=
          Metric.infDist_le_dist_of_mem (s := numericalRange A) (x := z) ⟨u, hu, rfl⟩
        rw [dist_eq_norm] at hle0
        rw [← hinneru] at hle0
        have hcoe : (ε : ℝ) = Metric.infDist z (numericalRange A) :=
          congrArg Subtype.val hεdef
        rwa [hcoe]
      have hscale : ‖inner ℂ x (g x)‖ = ‖x‖ ^ 2 * ‖inner ℂ u (g u)‖ := by
        conv_lhs => rw [← hxrepr]
        rw [map_smul, inner_smul_left, inner_smul_right, norm_mul, norm_mul, norm_conj]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), pow_two]
        ring
      calc
        ‖x‖ ^ 2 * (ε : ℝ) ≤ ‖x‖ ^ 2 * ‖inner ℂ u (g u)‖ :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg _)
        _ = ‖inner ℂ x (g x)‖ := hscale.symm
        _ = ‖inner ℂ (g x) x‖ := norm_inner_symm x (g x)
  have hεpos : (0 : NNReal) < ε := hε
  have hunit : IsUnit g :=
    ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map g (c := ε) hεpos key
  exact (spectrum.notMem_iff.mpr hunit) hz
lemma realLinear_image_sphere_eq_image_closedBall
    (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ) :
    F '' {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ = 1} =
      F '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hker : LinearMap.ker F.toLinearMap ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [finrank_euclideanSpace_fin, Complex.finrank_real_complex]
    norm_num
  obtain ⟨k, hk, hk0⟩ := (Submodule.ne_bot_iff (LinearMap.ker F.toLinearMap)).mp hker
  have hFk : F k = 0 := by simpa using hk
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, by simpa [mem_closedBall_zero_iff] using le_of_eq hx, rfl⟩
  · rintro z ⟨n, hn, rfl⟩
    have hnle : ‖n‖ ≤ 1 := by simpa [mem_closedBall_zero_iff] using hn
    obtain ⟨t, ht⟩ := realLinear_exists_unit_norm_add_kernel k hk0 n hnle
    refine ⟨n + t • k, ht, ?_⟩
    simp [hFk]
lemma realLinear_image_sphere_convex
    (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ) :
    Convex ℝ (F '' {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ = 1}) := by
  rw [realLinear_image_sphere_eq_image_closedBall F]
  simpa using
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).linear_image F.toLinearMap
abbrev Fin3Euclid := EuclideanSpace ℝ (Fin 3)
def fin2E0 : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 (0 : Fin 2) (1 : ℂ)
def fin2E1 : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 (1 : Fin 2) (1 : ℂ)
def blochMap (x : EuclideanSpace ℂ (Fin 2)) : Fin3Euclid :=
  !₂[2 * (conj (x 0) * x 1).re, 2 * (conj (x 0) * x 1).im, ‖x 0‖ ^ 2 - ‖x 1‖ ^ 2]
lemma blochMap_apply_zero (x : EuclideanSpace ℂ (Fin 2)) : blochMap x 0 = 2 * (conj (x 0) * x 1).re := by
  simp [blochMap]
lemma blochMap_apply_one (x : EuclideanSpace ℂ (Fin 2)) : blochMap x 1 = 2 * (conj (x 0) * x 1).im := by
  simp [blochMap]
lemma blochMap_apply_two (x : EuclideanSpace ℂ (Fin 2)) : blochMap x 2 = ‖x 0‖ ^ 2 - ‖x 1‖ ^ 2 := by
  simp [blochMap]
lemma blochMap_norm_sq (x : EuclideanSpace ℂ (Fin 2)) : ‖blochMap x‖ ^ 2 = (‖x‖ ^ 2) ^ 2 := by
  have hx : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  have hb : ‖blochMap x‖ ^ 2
      = (2 * (conj (x 0) * x 1).re) ^ 2 + (2 * (conj (x 0) * x 1).im) ^ 2
        + (‖x 0‖ ^ 2 - ‖x 1‖ ^ 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_three, blochMap]
  have hz : ‖conj (x 0) * x 1‖ ^ 2 = ‖x 0‖ ^ 2 * ‖x 1‖ ^ 2 := by
    rw [norm_mul, norm_conj]; ring
  have hs : (conj (x 0) * x 1).re ^ 2 + (conj (x 0) * x 1).im ^ 2
      = ‖conj (x 0) * x 1‖ ^ 2 := by
    rw [Complex.sq_norm]; simp [Complex.normSq_apply, pow_two]
  rw [hb, hx]
  nlinarith [hs, hz]
lemma blochMap_norm (x : EuclideanSpace ℂ (Fin 2)) (hx : ‖x‖ = 1) : ‖blochMap x‖ = 1 := by
  have h := blochMap_norm_sq x
  rw [hx] at h
  simp only [one_pow] at h
  rcases sq_eq_one_iff.mp h with h' | h'
  · exact h'
  · have := norm_nonneg (blochMap x); linarith
lemma inner_fin2 (x y : EuclideanSpace ℂ (Fin 2)) : inner ℂ x y = y 0 * conj (x 0) + y 1 * conj (x 1) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [RCLike.inner_apply]
lemma bloch_identity (α β γ δ x0 x1 : ℂ) (p q : ℝ)
    (hp : conj x0 * x0 = (p : ℂ)) (hq : conj x1 * x1 = (q : ℂ)) :
    conj x0 * x0 * α + conj x0 * x1 * β + conj x1 * x0 * γ + conj x1 * x1 * δ
      = ((p + q : ℝ) : ℂ) * ((α + δ) / 2)
        + ((2 * (conj x0 * x1).re : ℝ) : ℂ) * ((β + γ) / 2)
        + ((2 * (conj x0 * x1).im : ℝ) : ℂ) * (I * ((β - γ) / 2))
        + ((p - q : ℝ) : ℂ) * ((α - δ) / 2) := by
  have hconj : conj x1 * x0 = conj (conj x0 * x1) := by
    rw [map_mul, Complex.conj_conj]; ring
  rw [hp, hq, hconj]
  have hsplit : (conj x0 * x1) * β + conj (conj x0 * x1) * γ
      = ((β + γ) / 2) * ((conj x0 * x1) + conj (conj x0 * x1))
        + ((β - γ) / 2) * ((conj x0 * x1) - conj (conj x0 * x1)) := by
    ring
  rw [show ((p : ℂ) * α + (conj x0 * x1) * β + conj (conj x0 * x1) * γ + (q : ℂ) * δ)
      = (p : ℂ) * α + ((conj x0 * x1) * β + conj (conj x0 * x1) * γ) + (q : ℂ) * δ by ring]
  rw [hsplit, Complex.add_conj, Complex.sub_conj]
  push_cast
  ring
lemma inner_eq_bloch (A : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) (x : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ x (A x)
      = ((‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 : ℝ) : ℂ) *
          ((inner ℂ fin2E0 (A fin2E0) + inner ℂ fin2E1 (A fin2E1)) / 2)
        + ((2 * (conj (x 0) * x 1).re : ℝ) : ℂ) *
            ((inner ℂ fin2E0 (A fin2E1) + inner ℂ fin2E1 (A fin2E0)) / 2)
        + ((2 * (conj (x 0) * x 1).im : ℝ) : ℂ) *
            (Complex.I * ((inner ℂ fin2E0 (A fin2E1) - inner ℂ fin2E1 (A fin2E0)) / 2))
        + ((‖x 0‖ ^ 2 - ‖x 1‖ ^ 2 : ℝ) : ℂ) *
            ((inner ℂ fin2E0 (A fin2E0) - inner ℂ fin2E1 (A fin2E1)) / 2) := by
  have hinner : inner ℂ x (A x)
      = conj (x 0) * x 0 * inner ℂ fin2E0 (A fin2E0)
        + conj (x 0) * x 1 * inner ℂ fin2E0 (A fin2E1)
        + conj (x 1) * x 0 * inner ℂ fin2E1 (A fin2E0)
        + conj (x 1) * x 1 * inner ℂ fin2E1 (A fin2E1) := by
    have hxx : x = x 0 • fin2E0 + x 1 • fin2E1 := by
      ext j; fin_cases j <;> simp [fin2E0, fin2E1]
    have hAx : A x = x 0 • A fin2E0 + x 1 • A fin2E1 := by
      calc A x = A (x 0 • fin2E0 + x 1 • fin2E1) := congrArg A hxx
        _ = x 0 • A fin2E0 + x 1 • A fin2E1 := by rw [map_add, map_smul, map_smul]
    have h0 : ∀ y : EuclideanSpace ℂ (Fin 2), inner ℂ fin2E0 y = y 0 := by
      intro y; rw [PiLp.inner_apply, Fin.sum_univ_two]; simp [fin2E0]
    have h1 : ∀ y : EuclideanSpace ℂ (Fin 2), inner ℂ fin2E1 y = y 1 := by
      intro y; rw [PiLp.inner_apply, Fin.sum_univ_two]; simp [fin2E1]
    rw [inner_fin2 x (A x), hAx]
    simp only [PiLp.add_apply, PiLp.smul_apply]
    rw [← h0 (A fin2E0), ← h1 (A fin2E0), ← h0 (A fin2E1), ← h1 (A fin2E1)]
    ring
  have h0 : conj (x 0) * x 0 = ((‖x 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.normSq_eq_conj_mul_self (z := x 0)).symm
  have h1 : conj (x 1) * x 1 = ((‖x 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.normSq_eq_conj_mul_self (z := x 1)).symm
  rw [hinner]
  exact bloch_identity _ _ _ _ _ _ _ _ h0 h1
lemma blochMap_surj (u : Fin3Euclid) (hu : ‖u‖ = 1) : ∃ x : EuclideanSpace ℂ (Fin 2), ‖x‖ = 1 ∧ blochMap x = u := by
  have hs : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have h := (EuclideanSpace.real_norm_sq_eq u).symm
    simpa [Fin.sum_univ_three, hu] using h
  by_cases h2 : u 2 = -1
  · refine ⟨PiLp.single 2 1 1, ?_, ?_⟩
    · simp
    · have h0 : u 0 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      have h1 : u 1 = 0 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      ext j
      fin_cases j <;> simp [blochMap_apply_zero, blochMap_apply_one, blochMap_apply_two, h0, h1, h2]
  · have hle : u 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    have habs : |u 2| ≤ 1 := by rwa [← sq_le_one_iff_abs_le_one]
    have h2' : -1 < u 2 := lt_of_le_of_ne (abs_le.mp habs).1 (Ne.symm h2)
    have hpos : 0 < (1 + u 2) / 2 := by linarith
    set s : ℝ := Real.sqrt ((1 + u 2) / 2) with hsdef
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hssq : s ^ 2 = (1 + u 2) / 2 := by
      rw [hsdef]; exact Real.sq_sqrt hpos.le
    set t : ℂ := (u 0 : ℂ) + Complex.I * (u 1 : ℂ) with htdef
    have ht_norm : ‖t‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
      rw [htdef, Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have htnorm2 : ‖t / (2 * (s : ℂ))‖ ^ 2 = (u 0 ^ 2 + u 1 ^ 2) / (4 * s ^ 2) := by
      rw [norm_div, div_pow, ht_norm]
      have hden : ‖(2 * (s : ℂ))‖ ^ 2 = 4 * s ^ 2 := by
        rw [norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
        rw [mul_pow, sq_abs]
        norm_num
      rw [hden]
    have hx1norm : ‖t / (2 * (s : ℂ))‖ ^ 2 = (1 - u 2) / 2 := by
      rw [htnorm2, hssq]
      have hne : (1 + u 2) ≠ 0 := by linarith
      have hsq : u 0 ^ 2 + u 1 ^ 2 = 1 - u 2 ^ 2 := by linarith
      rw [hsq]
      field_simp
      ring
    refine ⟨!₂[(s : ℂ), t / (2 * (s : ℂ))], ?_, ?_⟩
    · have hx0n : ‖(!₂[(s : ℂ), t / (2 * (s : ℂ))] : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 = s ^ 2 := by
        show ‖(s : ℂ)‖ ^ 2 = s ^ 2
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hx1n : ‖(!₂[(s : ℂ), t / (2 * (s : ℂ))] : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2 = (1 - u 2) / 2 := hx1norm
      have hsq : ‖(!₂[(s : ℂ), t / (2 * (s : ℂ))] : EuclideanSpace ℂ (Fin 2))‖ ^ 2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, hx0n, hx1n, hssq]
        ring
      rcases sq_eq_one_iff.mp hsq with h | h
      · exact h
      · have hnn := norm_nonneg (!₂[(s : ℂ), t / (2 * (s : ℂ))] : EuclideanSpace ℂ (Fin 2))
        rw [h] at hnn
        linarith
    · set x : EuclideanSpace ℂ (Fin 2) := !₂[(s : ℂ), t / (2 * (s : ℂ))] with hxdef
      have hx0v : x 0 = (s : ℂ) := by simp [x]
      have hx1v : x 1 = t / (2 * (s : ℂ)) := by simp [x]
      have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
      have hcx : conj (x 0) * x 1 = t / 2 := by
        rw [hx0v, hx1v, Complex.conj_ofReal]
        field_simp
      have hx0n : ‖x 0‖ ^ 2 = s ^ 2 := by
        rw [hx0v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hx1n : ‖x 1‖ ^ 2 = (1 - u 2) / 2 := by
        rw [hx1v]; exact hx1norm
      have htr : (t / 2).re = u 0 / 2 := by simp [htdef]
      have hti : (t / 2).im = u 1 / 2 := by simp [htdef]
      ext j
      fin_cases j
      · show blochMap x 0 = u 0
        rw [blochMap_apply_zero, hcx, htr]; ring
      · show blochMap x 1 = u 1
        rw [blochMap_apply_one, hcx, hti]; ring
      · show blochMap x 2 = u 2
        rw [blochMap_apply_two, hx0n, hx1n, hssq]
        ring
theorem numericalRange_fin2_param
    (A : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    ∃ (c : ℂ) (F : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ),
      numericalRange A =
        (fun z : ℂ => c + z) '' (F '' {u : EuclideanSpace ℝ (Fin 3) | ‖u‖ = 1}) := by
  let α : ℂ := inner ℂ fin2E0 (A fin2E0)
  let β : ℂ := inner ℂ fin2E0 (A fin2E1)
  let γ : ℂ := inner ℂ fin2E1 (A fin2E0)
  let δ : ℂ := inner ℂ fin2E1 (A fin2E1)
  let c : ℂ := (α + δ) / 2
  let a : ℂ := (α - δ) / 2
  let b0 : ℂ := (β + γ) / 2
  let b1 : ℂ := Complex.I * ((β - γ) / 2)
  let F : Fin3Euclid →L[ℝ] ℂ :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).smulRight b0 +
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).smulRight b1 +
      (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).smulRight a
  have hF : ∀ u : Fin3Euclid, F u = u 0 • b0 + u 1 • b1 + u 2 • a := by
    intro u
    simp [F, ContinuousLinearMap.smulRight_apply, EuclideanSpace.proj]
  have hpt : ∀ x : EuclideanSpace ℂ (Fin 2), ‖x‖ = 1 → inner ℂ x (A x) = c + F (blochMap x) := by
    intro x hx
    have h2 : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    have hp : ((‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h2, hx]; norm_num
    have h := inner_eq_bloch A x
    rw [hp, one_mul] at h
    rw [h, hF]
    simp only [blochMap_apply_zero, blochMap_apply_one, blochMap_apply_two, α, β, γ, δ, c, a, b0, b1]
    rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  refine ⟨c, F, ?_⟩
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨F (blochMap x), ⟨blochMap x, blochMap_norm x hx, rfl⟩, (hpt x hx).symm⟩
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := blochMap_surj u hu
    exact ⟨x, hx, hpt x hx⟩
lemma numericalRange_convex_fin2
    (A : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :
    Convex ℝ (numericalRange A) := by
  obtain ⟨c, F, hAF⟩ := numericalRange_fin2_param A
  rw [hAF]
  simpa [add_comm] using (realLinear_image_sphere_convex F).translate c
lemma compression_apply_of_mem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (hx : A (x : H) ∈ E) :
    (compression A E x : H) = A (x : H) := by
  rw [compression, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact congrArg Subtype.val
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨A x, hx⟩)
lemma compression_pow_apply_of_mem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : E) (k : ℕ)
    (h : ∀ j ≤ k, (A ^ j) (x : H) ∈ E) :
    (((compression A E) ^ k) x : H) = (A ^ k) (x : H) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hxE : A (x : H) ∈ E := h 1 (by omega)
    have hstep : (compression A E x : H) = A (x : H) :=
      compression_apply_of_mem A E x hxE
    have ih' : ∀ j ≤ k,
        (A ^ j) (((compression A E) x : E) : H) ∈ E := by
      intro j hj
      rw [hstep]
      have hp : (A ^ j) (A (x : H)) = (A ^ (j+1)) (x : H) := by
        rw [pow_succ, ContinuousLinearMap.mul_apply]
      rw [hp]
      exact h (j+1) (Nat.succ_le_succ hj)
    have key := ih (compression A E x) ih'
    calc
      ((((compression A E) ^ k) * (compression A E)) x : H)
          = (((compression A E) ^ k) ((compression A E) x) : H) := rfl
      _ = (A ^ k) ((compression A E x : E) : H) := key
      _ = (A ^ k) (A (x : H)) := by rw [hstep]
      _ = (A ^ (k+1)) (x : H) := by
            rw [pow_succ, ContinuousLinearMap.mul_apply]
lemma tensorInclusion_tmul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : Submodule ℂ H) (m : ℕ)
    (x : E) (f : CoeffSpace m) :
    tensorInclusion E m (↑(x ⊗ₜ[ℂ] f) : Amplification E m) =
      (↑((x : H) ⊗ₜ[ℂ] f) : Amplification H m) := by
  rw [tensorInclusion_coe]
  congr 1
lemma tensorInclusion_sum_tmul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (E : Submodule ℂ H) (m : ℕ)
    {ι : Type*} (s : Finset ι) (x : ι → E) (f : ι → CoeffSpace m) :
    tensorInclusion E m (↑(∑ i ∈ s, x i ⊗ₜ[ℂ] f i) : Amplification E m) =
      (↑(∑ i ∈ s, (x i : H) ⊗ₜ[ℂ] f i) : Amplification H m) := by
  rw [tensorInclusion_coe]
  congr 1
  rw [TensorProduct.mapIsometry_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [TensorProduct.map_tmul]
  rfl
lemma tensorInclusion_tensorOp_tmul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {m : ℕ} (E : Submodule ℂ H)
    (C : E →L[ℂ] E) (B : Coeff m) (x : E) (f : CoeffSpace m) :
    tensorInclusion E m (tensorOp C B (↑(x ⊗ₜ[ℂ] f) : Amplification E m)) =
      (↑(((C x : E) : H) ⊗ₜ[ℂ]
        (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) B) f) :
        Amplification H m) := by
  rw [tensorOp_tmul, tensorInclusion_tmul]
lemma tensorInclusion_polynomialEval_tmul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {m d : ℕ} (A : H →L[ℂ] H)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (B : Fin (d + 1) → Coeff m) (x : E) (f : CoeffSpace m)
    (hx : ∀ j : Fin (d + 1), (A ^ j.val) (x : H) ∈ E) :
    tensorInclusion E m (polynomialEval (compression A E) B
        (↑(x ⊗ₜ[ℂ] f) : Amplification E m)) =
      polynomialEval A B (↑((x : H) ⊗ₜ[ℂ] f) : Amplification H m) := by
  simp only [polynomialEval, ContinuousLinearMap.sum_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [tensorInclusion_tensorOp_tmul, tensorOp_tmul]
  have hle : k.val ≤ d := Nat.lt_succ_iff.mp k.isLt
  have hmem : ∀ j ≤ k.val, (A ^ j) (x : H) ∈ E := by
    intro j hj
    exact hx ⟨j, Nat.lt_succ_of_le (le_trans hj hle)⟩
  rw [compression_pow_apply_of_mem A E x k.val hmem]
lemma tensorInclusion_polynomialEval_sum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {m d : ℕ} (A : H →L[ℂ] H)
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (B : Fin (d + 1) → Coeff m) {ι : Type*} (s : Finset ι)
    (x : ι → E) (f : ι → CoeffSpace m)
    (hx : ∀ i ∈ s, ∀ j : Fin (d + 1), (A ^ j.val) (x i : H) ∈ E) :
    tensorInclusion E m (polynomialEval (compression A E) B
        (↑(∑ i ∈ s, x i ⊗ₜ[ℂ] f i) : Amplification E m)) =
      polynomialEval A B (↑(∑ i ∈ s, (x i : H) ⊗ₜ[ℂ] f i) : Amplification H m) := by
  have hcoeE : (↑(∑ i ∈ s, x i ⊗ₜ[ℂ] f i) : Amplification E m)
      = ∑ i ∈ s, (↑(x i ⊗ₜ[ℂ] f i) : Amplification E m) := by
    change UniformSpace.Completion.toCompl _ = _
    rw [map_sum]
    rfl
  have hcoeH : (↑(∑ i ∈ s, (x i : H) ⊗ₜ[ℂ] f i) : Amplification H m)
      = ∑ i ∈ s, (↑((x i : H) ⊗ₜ[ℂ] f i) : Amplification H m) := by
    change UniformSpace.Completion.toCompl _ = _
    rw [map_sum]
    rfl
  rw [hcoeE, hcoeH]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact tensorInclusion_polynomialEval_tmul A E B (x i) (f i) (hx i hi)
lemma polynomial_aeval_isUnit_of_forall_eval_ne_zero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (A : H →L[ℂ] H) (p : Polynomial ℂ)
    (hp : ∀ z ∈ spectrum ℂ A, p.eval z ≠ 0) :
    IsUnit (Polynomial.aeval A p) := by
  by_contra h
  have h0 : (0 : ℂ) ∈ spectrum ℂ (Polynomial.aeval A p) := by
    rw [spectrum.zero_mem_iff]
    exact h
  rw [spectrum.map_polynomial_aeval] at h0
  obtain ⟨z, hz, hz0⟩ := h0
  exact hp z hz hz0
lemma norm_fin2_sq (d : EuclideanSpace ℂ (Fin 2)) :
    ‖d‖ ^ 2 = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
lemma inner_toEuclideanCLM_fin2b (b : Matrix (Fin 2) (Fin 2) ℂ) (u : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ u (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) b u)
      = (starRingEnd ℂ) (u 0) * (b 0 0 * u 0 + b 0 1 * u 1)
        + (starRingEnd ℂ) (u 1) * (b 1 0 * u 0 + b 1 1 * u 1) := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_apply, dotProduct, Fin.sum_univ_two,
    RCLike.inner_apply, Matrix.row_apply]
  ring
lemma inner_orthonormal_pair (A : H →L[ℂ] H) (e0 e1 : H)
    (h00 : inner ℂ e0 e0 = 1) (h11 : inner ℂ e1 e1 = 1) (h01 : inner ℂ e0 e1 = 0)
    (c0 c1 : ℂ) :
    inner ℂ (c0 • e0 + c1 • e1) (A (c0 • e0 + c1 • e1)) =
      (starRingEnd ℂ) c0 * (c0 * inner ℂ e0 (A e0) + c1 * inner ℂ e0 (A e1))
      + (starRingEnd ℂ) c1 * (c0 * inner ℂ e1 (A e0) + c1 * inner ℂ e1 (A e1)) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h00, h11, h01, inner_zero_left, mul_zero, add_zero, zero_add,
    zero_mul, star_zero, star_one, mul_one, one_mul]
  ring
lemma inner_self_combination (e0 e1 : H)
    (h00 : inner ℂ e0 e0 = 1) (h11 : inner ℂ e1 e1 = 1) (h01 : inner ℂ e0 e1 = 0)
    (h10 : inner ℂ e1 e0 = 0) (c0 c1 : ℂ) :
    inner ℂ (c0 • e0 + c1 • e1) (c0 • e0 + c1 • e1)
      = (starRingEnd ℂ) c0 * c0 + (starRingEnd ℂ) c1 * c1 := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h00, h11, h01, h10, mul_one, mul_zero, add_zero, zero_add, zero_mul,
    star_zero]
  ring
lemma norm_sq_smul_pair (e0 e1 : H)
    (h00 : inner ℂ e0 e0 = 1) (h11 : inner ℂ e1 e1 = 1) (h01 : inner ℂ e0 e1 = 0)
    (c0 c1 : ℂ) : ‖c0 • e0 + c1 • e1‖ ^ 2 = ‖c0‖ ^ 2 + ‖c1‖ ^ 2 := by
  have h10 : inner ℂ e1 e0 = 0 := by
    rw [← inner_conj_symm, h01]; simp
  have hinner : inner ℂ (c0 • e0 + c1 • e1) (c0 • e0 + c1 • e1)
      = ((‖c0‖ ^ 2 + ‖c1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_combination e0 e1 h00 h11 h01 h10, RCLike.conj_mul, RCLike.conj_mul]
    norm_cast
  have h1 : inner ℂ (c0 • e0 + c1 • e1) (c0 • e0 + c1 • e1)
      = ((‖c0 • e0 + c1 • e1‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h2 : ((‖c0 • e0 + c1 • e1‖ ^ 2 : ℝ) : ℂ) = ((‖c0‖ ^ 2 + ‖c1‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h1, hinner]
  exact_mod_cast h2
lemma norm_pairEmb (e0 e1 : H)
    (h00 : inner ℂ e0 e0 = 1) (h11 : inner ℂ e1 e1 = 1) (h01 : inner ℂ e0 e1 = 0)
    (d : EuclideanSpace ℂ (Fin 2)) :
    ‖d 0 • e0 + d 1 • e1‖ = ‖d‖ := by
  have h1 : ‖d 0 • e0 + d 1 • e1‖ ^ 2 = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 :=
    norm_sq_smul_pair e0 e1 h00 h11 h01 (d 0) (d 1)
  have h2 : ‖d‖ ^ 2 = ‖d 0‖ ^ 2 + ‖d 1‖ ^ 2 := norm_fin2_sq d
  have h3 : ‖d 0 • e0 + d 1 • e1‖ ^ 2 = ‖d‖ ^ 2 := h1.trans h2.symm
  nlinarith [norm_nonneg (d 0 • e0 + d 1 • e1), norm_nonneg d]
noncomputable def pairMatrix (A : H →L[ℂ] H) (e0 e1 : H) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![inner ℂ e0 (A e0), inner ℂ e0 (A e1); inner ℂ e1 (A e0), inner ℂ e1 (A e1)]
lemma inner_pair_eq_euclidean (A : H →L[ℂ] H) (e0 e1 : H)
    (h00 : inner ℂ e0 e0 = 1) (h11 : inner ℂ e1 e1 = 1) (h01 : inner ℂ e0 e1 = 0)
    (d : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (d 0 • e0 + d 1 • e1) (A (d 0 • e0 + d 1 • e1)) =
      inner ℂ d (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (pairMatrix A e0 e1) d) := by
  rw [inner_orthonormal_pair A e0 e1 h00 h11 h01, inner_toEuclideanCLM_fin2b]
  simp only [pairMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.head_cons, Matrix.tail_cons]
  ring
lemma numericalRange_convex_H (A : H →L[ℂ] H) : Convex ℝ (numericalRange A) := by
  rw [convex_iff_forall_pos]
  intro z1 hz1 z2 hz2 a b ha hb hab
  obtain ⟨x, hx, rfl⟩ := hz1
  obtain ⟨y, hy, rfl⟩ := hz2
  have hxx : inner ℂ x x = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  set α : ℂ := inner ℂ x y with hα
  by_cases hdep : y - α • x = 0
  · have hyx : y = α • x := sub_eq_zero.mp hdep
    have hα1 : ‖α‖ = 1 := by
      rw [hyx, norm_smul, hx, mul_one] at hy
      exact hy
    have hval : inner ℂ y (A y) = inner ℂ x (A x) := by
      rw [hyx, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
        RCLike.conj_mul, hα1]
      norm_num
    refine ⟨x, hx, ?_⟩
    rw [← hval, ← add_smul, hab, one_smul]
  · have hrpos : 0 < ‖y - α • x‖ := norm_pos_iff.mpr hdep
    set e0 : H := x with he0
    set e1 : H := ((‖y - α • x‖ : ℂ))⁻¹ • (y - α • x) with he1
    have h00 : inner ℂ e0 e0 = 1 := by rw [he0]; exact hxx
    have he1norm : ‖e1‖ = 1 := by
      rw [he1, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hrpos, inv_mul_cancel₀ hrpos.ne']
    have h11 : inner ℂ e1 e1 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, he1norm]; norm_num
    have h01 : inner ℂ e0 e1 = 0 := by
      rw [he0, he1, inner_smul_right]
      have hz : inner ℂ x (y - α • x) = 0 := by
        rw [inner_sub_right, inner_smul_right, ← hα, hxx, mul_one, sub_self]
      rw [hz, mul_zero]
    have hydecomp : y = α • e0 + ((‖y - α • x‖ : ℂ)) • e1 := by
      rw [he0, he1, smul_smul]
      have hne : ((‖y - α • x‖ : ℂ)) ≠ 0 := by
        exact_mod_cast hrpos.ne'
      rw [mul_inv_cancel₀ hne, one_smul]
      abel
    let d1 : EuclideanSpace ℂ (Fin 2) := !₂[(1 : ℂ), (0 : ℂ)]
    let d2 : EuclideanSpace ℂ (Fin 2) := !₂[α, ((‖y - α • x‖ : ℂ))]
    have hd1sum : d1 0 • e0 + d1 1 • e1 = x := by
      simp [d1, he0]
    have hd2sum : d2 0 • e0 + d2 1 • e1 = y := by
      have hpdf : d2 0 = α ∧ d2 1 = ((‖y - α • x‖ : ℂ)) := by
        simp [d2]
      rw [hpdf.1, hpdf.2]
      exact hydecomp.symm
    have hd1 : ‖d1‖ = 1 := by
      have h : ‖d1‖ ^ 2 = 1 := by
        rw [norm_fin2_sq]; simp [d1]
      nlinarith [norm_nonneg d1]
    have hd2 : ‖d2‖ = 1 := by
      have hsq : ‖d2‖ ^ 2 = ‖α‖ ^ 2 + ‖((‖y - α • x‖ : ℂ))‖ ^ 2 := by
        rw [norm_fin2_sq]; simp [d2]
      have hp : ‖α • e0 + ((‖y - α • x‖ : ℂ)) • e1‖ ^ 2
          = ‖α‖ ^ 2 + ‖((‖y - α • x‖ : ℂ))‖ ^ 2 :=
        norm_sq_smul_pair e0 e1 h00 h11 h01 α _
      rw [← hydecomp, hy] at hp
      have h2 : ‖d2‖ ^ 2 = 1 := by
        rw [hsq, ← hp]; norm_num
      nlinarith [norm_nonneg d2]
    let B : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
      Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (pairMatrix A e0 e1)
    have hd1mem : inner ℂ d1 (B d1) = inner ℂ x (A x) := by
      rw [← inner_pair_eq_euclidean A e0 e1 h00 h11 h01 d1, hd1sum]
    have hd2mem : inner ℂ d2 (B d2) = inner ℂ y (A y) := by
      rw [← inner_pair_eq_euclidean A e0 e1 h00 h11 h01 d2, hd2sum]
    have hBmem : a • inner ℂ d1 (B d1) + b • inner ℂ d2 (B d2) ∈ numericalRange B :=
      convex_iff_forall_pos.mp (numericalRange_convex_fin2 B)
        ⟨_, hd1, rfl⟩ ⟨_, hd2, rfl⟩ ha hb hab
    obtain ⟨d3, hd3, hd3eq⟩ := hBmem
    refine ⟨d3 0 • e0 + d3 1 • e1, ?_, ?_⟩
    · rw [norm_pairEmb e0 e1 h00 h11 h01 d3, hd3]
    · rw [inner_pair_eq_euclidean A e0 e1 h00 h11 h01 d3, hd3eq, hd1mem, hd2mem]
lemma inner_compression_coe (A : H →L[ℂ] H) (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (u : V) : inner ℂ u (compression A V u) = inner ℂ (u : H) (A (u : H)) := by
  have hcomp : compression A V u = V.orthogonalProjectionOnto (A (u : H)) := by
    simp [compression]
  rw [hcomp]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left u (A (u : H))
lemma numericalRange_compression_subset (A : H →L[ℂ] H) (V : Submodule ℂ H)
    [V.HasOrthogonalProjection] :
    numericalRange (compression A V) ⊆ numericalRange A := by
  rintro z ⟨u, hu, rfl⟩
  refine ⟨(u : H), ?_, (inner_compression_coe A V u).symm⟩
  rw [Submodule.norm_coe]
  exact hu
lemma numericalRange_conj_linearIsometryEquiv
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (e : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2)) (C : K →L[ℂ] K) :
    numericalRange ((e.toLinearIsometry.toContinuousLinearMap).comp
        (C.comp (e.symm.toLinearIsometry.toContinuousLinearMap))) =
      numericalRange C := by
  set B : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    (e.toLinearIsometry.toContinuousLinearMap).comp
      (C.comp (e.symm.toLinearIsometry.toContinuousLinearMap)) with hBdef
  have hBu : ∀ u : K, B (e u) = e (C u) := by
    intro u
    simp only [hBdef, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    rw [LinearIsometryEquiv.symm_apply_apply]
  have hBy : ∀ y : EuclideanSpace ℂ (Fin 2), B y = e (C (e.symm y)) := by
    intro y
    conv_lhs => rw [← e.apply_symm_apply y]
    exact hBu (e.symm y)
  ext z
  constructor
  · rintro ⟨y, hy, hval⟩
    refine ⟨e.symm y, ?_, ?_⟩
    · rw [e.symm.norm_map]; exact hy
    · calc inner ℂ (e.symm y) (C (e.symm y))
          = inner ℂ (e (e.symm y)) (e (C (e.symm y))) := (e.inner_map_map _ _).symm
        _ = inner ℂ y (e (C (e.symm y))) := by rw [e.apply_symm_apply]
        _ = inner ℂ y (B y) := by rw [hBy]
        _ = z := hval
  · rintro ⟨u, hu, hval⟩
    refine ⟨e u, ?_, ?_⟩
    · rw [e.norm_map]; exact hu
    · calc inner ℂ (e u) (B (e u)) = inner ℂ (e u) (e (C u)) := by rw [hBu]
        _ = inner ℂ u (C u) := e.inner_map_map u (C u)
        _ = z := hval
theorem numericalRange_convex :
    ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (A : H →L[ℂ] H), Convex ℝ (numericalRange A) := by
  intro H _ _ _ A
  rw [convex_iff_forall_pos]
  intro z1 hz1 z2 hz2 a b ha hb hab
  obtain ⟨x, hx, rfl⟩ := hz1
  obtain ⟨y, hy, rfl⟩ := hz2
  by_cases hind : LinearIndependent ℂ ![x, y]
  · let V : Submodule ℂ H := Submodule.span ℂ (Set.range ![x, y])
    have hVfin : FiniteDimensional ℂ V :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range (![x, y] : Fin 2 → H))
    haveI := hVfin
    have hVcomp : CompleteSpace V := FiniteDimensional.complete ℂ V
    haveI := hVcomp
    have hVproj : V.HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace V
    haveI := hVproj
    let C : V →L[ℂ] V := compression A V
    have hxV : x ∈ V := Submodule.subset_span (Set.mem_range_self (0 : Fin 2))
    have hyV : y ∈ V := Submodule.subset_span (Set.mem_range_self (1 : Fin 2))
    have hfr : Module.finrank ℂ V = 2 := by
      have h := finrank_span_eq_card (R := ℂ) hind
      simpa using h
    let e : V ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
      ((stdOrthonormalBasis ℂ V).reindex (finCongr hfr)).repr
    let B : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
      (e.toLinearIsometry.toContinuousLinearMap).comp
        (C.comp (e.symm.toLinearIsometry.toContinuousLinearMap))
    have hBeq : numericalRange B = numericalRange C :=
      numericalRange_conj_linearIsometryEquiv e C
    have hz1B : inner ℂ (e ⟨x, hxV⟩) (B (e ⟨x, hxV⟩)) = inner ℂ x (A x) := by
      have hBu : B (e ⟨x, hxV⟩) = e (C ⟨x, hxV⟩) := by
        simp only [B, ContinuousLinearMap.comp_apply,
          LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
        rw [LinearIsometryEquiv.symm_apply_apply]
      calc inner ℂ (e ⟨x, hxV⟩) (B (e ⟨x, hxV⟩))
          = inner ℂ (e ⟨x, hxV⟩) (e (C ⟨x, hxV⟩)) := by rw [hBu]
        _ = inner ℂ (⟨x, hxV⟩ : V) (C ⟨x, hxV⟩) := e.inner_map_map _ _
        _ = inner ℂ x (A x) := inner_compression_coe A V ⟨x, hxV⟩
    have hz2B : inner ℂ (e ⟨y, hyV⟩) (B (e ⟨y, hyV⟩)) = inner ℂ y (A y) := by
      have hBu : B (e ⟨y, hyV⟩) = e (C ⟨y, hyV⟩) := by
        simp only [B, ContinuousLinearMap.comp_apply,
          LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
        rw [LinearIsometryEquiv.symm_apply_apply]
      calc inner ℂ (e ⟨y, hyV⟩) (B (e ⟨y, hyV⟩))
          = inner ℂ (e ⟨y, hyV⟩) (e (C ⟨y, hyV⟩)) := by rw [hBu]
        _ = inner ℂ (⟨y, hyV⟩ : V) (C ⟨y, hyV⟩) := e.inner_map_map _ _
        _ = inner ℂ y (A y) := inner_compression_coe A V ⟨y, hyV⟩
    have hmem1 : inner ℂ (e ⟨x, hxV⟩) (B (e ⟨x, hxV⟩)) ∈ numericalRange B := by
      refine ⟨e ⟨x, hxV⟩, ?_, rfl⟩
      rw [e.norm_map]
      simpa using hx
    have hmem2 : inner ℂ (e ⟨y, hyV⟩) (B (e ⟨y, hyV⟩)) ∈ numericalRange B := by
      refine ⟨e ⟨y, hyV⟩, ?_, rfl⟩
      rw [e.norm_map]
      simpa using hy
    have hconv := (convex_iff_forall_pos.mp (numericalRange_convex_fin2 B)) hmem1 hmem2 ha hb hab
    rw [hz1B, hz2B, hBeq] at hconv
    exact numericalRange_compression_subset A V hconv
  · have hxne : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; exact zero_ne_one hx
    have hdep : ∃ c : ℂ, c • x = y := by
      by_contra h
      exact hind ((LinearIndependent.pair_iff' hxne).mpr (fun c hc => h ⟨c, hc⟩))
    obtain ⟨c, hc⟩ := hdep
    have hcnorm : ‖c‖ = 1 := by
      have h1 : ‖y‖ = ‖c‖ * ‖x‖ := by rw [← hc, norm_smul]
      rw [hy, hx, mul_one] at h1
      exact h1.symm
    have hcc : (starRingEnd ℂ) c * c = 1 := by
      have h1 : ((Complex.normSq c : ℝ) : ℂ) = (starRingEnd ℂ) c * c :=
        Complex.normSq_eq_conj_mul_self
      rw [← h1, Complex.normSq_eq_norm_sq, hcnorm]
      norm_num
    have hz2 : inner ℂ y (A y) = inner ℂ x (A x) := by
      rw [← hc, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hcc, one_mul]
    have hgoal : a • inner ℂ x (A x) + b • inner ℂ y (A y) = inner ℂ x (A x) := by
      rw [hz2, ← add_smul, hab, one_smul]
    rw [hgoal]
    exact ⟨x, hx, rfl⟩
theorem numericalClosure_geometry (A : H →L[ℂ] H) :
    IsCompact (numericalClosure A) ∧ Convex ℝ (numericalClosure A) ∧
      spectrum ℂ A ⊆ numericalClosure A := by
  refine ⟨numericalClosure_isCompact A, ?_, spectrum_subset_numericalClosure A⟩
  exact (numericalRange_convex_H A).closure
omit [CompleteSpace H] in
theorem exists_finite_compression {m d : ℕ} (A : H →L[ℂ] H)
    (B : Fin (d + 1) → Coeff m) (ξ : H ⊗[ℂ] CoeffSpace m) :
    ∃ (E : Submodule ℂ H) (hE : FiniteDimensional ℂ E),
      letI : FiniteDimensional ℂ E := hE
      ∃ η : Amplification E m,
        tensorInclusion E m η = (↑ξ : Amplification H m) ∧
        tensorInclusion E m (polynomialEval (compression A E) B η) =
          polynomialEval A B (↑ξ) := by
  classical
  obtain ⟨S, hS⟩ :=
    TensorProduct.exists_finset (R := ℂ) (M := H) (N := CoeffSpace m) ξ
  let G : Set H :=
    Set.range (fun q : S × Fin (d + 1) =>
      (A ^ q.2.val) (q.1 : H × CoeffSpace m).1)
  have hGfin : G.Finite := by
    have huniv : (Set.univ : Set (S × Fin (d + 1))).Finite := Set.finite_univ
    simpa [G] using huniv.image
      (fun q : S × Fin (d + 1) => (A ^ q.2.val) (q.1 : H × CoeffSpace m).1)
  let E : Submodule ℂ H := Submodule.span ℂ G
  have hE : FiniteDimensional ℂ E := FiniteDimensional.span_of_finite ℂ hGfin
  have hmem : ∀ p : S, (p.1 : H × CoeffSpace m).1 ∈ E := by
    intro p
    apply Submodule.subset_span
    refine ⟨(p, ⟨0, Nat.succ_pos d⟩), ?_⟩
    simp
  let x : S → E := fun p => ⟨(p.1 : H × CoeffSpace m).1, hmem p⟩
  let f : S → CoeffSpace m := fun p => (p.1 : H × CoeffSpace m).2
  refine ⟨E, hE, ?_⟩
  letI : FiniteDimensional ℂ E := hE
  have hx : ∀ p : S, ∀ j : Fin (d + 1), (A ^ j.val) (x p : H) ∈ E := by
    intro p j
    apply Submodule.subset_span
    exact ⟨(p, j), rfl⟩
  have hsum_eq : (∑ p : S, (x p : H) ⊗ₜ[ℂ] f p) =
      ∑ i ∈ S, i.1 ⊗ₜ[ℂ] i.2 := by
    rw [show (∑ p : S, (x p : H) ⊗ₜ[ℂ] f p)
        = ∑ p : S,
          ((p : H × CoeffSpace m).1 ⊗ₜ[ℂ] (p : H × CoeffSpace m).2) from by
      apply Finset.sum_congr rfl
      intro p _
      rfl]
    exact Finset.sum_coe_sort S (fun i : H × CoeffSpace m => i.1 ⊗ₜ[ℂ] i.2)
  refine ⟨(↑(∑ p : S, x p ⊗ₜ[ℂ] f p) : Amplification E m), ?_, ?_⟩
  · rw [tensorInclusion_sum_tmul]
    rw [hsum_eq, ← hS]
  · rw [tensorInclusion_polynomialEval_sum A E B Finset.univ x f
      (fun p _ j => hx p j)]
    rw [hsum_eq, ← hS]
theorem rational_denominator_isUnit [Nontrivial H] (A : H →L[ℂ] H)
    {m : ℕ} (R : RationalMatrix m) (hR : numericalClosure A ⊆ poleFreeSet R)
    (i j : Fin m) : IsUnit (Polynomial.aeval A (R i j).denom) := by
  refine polynomial_aeval_isUnit_of_forall_eval_ne_zero A (R i j).denom ?_
  intro z hz
  exact hR (spectrum_subset_numericalClosure A hz) i j
theorem zeroConclusion [Subsingleton H] (A : H →L[ℂ] H) : ZeroConclusion A := by
  have hrange : numericalRange A = ∅ := numericalRange_eq_empty_of_subsingleton A
  refine ⟨hrange, ?_, ?_⟩
  · intro m F
    rw [hrange, normSup_empty]
  · intro m _
    haveI : Subsingleton (Amplification H m) := subsingleton_amplification m
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T
      ext v
      exact Subsingleton.elim _ _
    · intro d B
      refine ⟨?_, ?_⟩
      · ext v
        exact Subsingleton.elim _ _
      · have h0 : polynomialEval A B = 0 := by
          ext v
          exact Subsingleton.elim _ _
        simp [h0, hrange, normSup_empty]
    · intro U F
      refine ⟨?_, ?_⟩
      · ext v
        exact Subsingleton.elim _ _
      · have h0 : holomorphicEval A U F = 0 := by
          ext v
          exact Subsingleton.elim _ _
        simp [h0, hrange, normSup_empty]
    · intro R
      refine ⟨?_, ?_⟩
      · ext v
        exact Subsingleton.elim _ _
      · have h0 : rationalEval A R = 0 := by
          ext v
          exact Subsingleton.elim _ _
        simp [h0, hrange, normSup_empty]
end HilbertCrouzeix

end

end OAI
