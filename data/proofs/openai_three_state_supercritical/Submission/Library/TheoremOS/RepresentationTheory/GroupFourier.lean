import Mathlib
import Submission.Library.TheoremOS.Probability.FiniteProbability

/-!
# Harmonic analysis on finite groups: convolution, Fourier transforms and Hilbert–Schmidt norms

Laws on a finite group `G`: convolution `(p * q)(g) = ∑ₓ p x q (x⁻¹ g)` over any semiring
(`groupConv`, associative with unit `deltaOne`) and convolution powers `groupConvPow` with
`p^{*(s+t)} = p^{*s} * p^{*t}`; convolutions and powers of distributions are distributions, the
uniform law absorbs every distribution, and total variation contracts under convolution
(`tvDist_groupConv_left_le`) with `‖p * q - u‖_TV ≤ 2 ‖p - u‖_TV ‖q - u‖_TV`
(`tvDist_groupConv_uniform_le`, `tvDist_groupConvPow_add_le`). The law of `f : Ω → β` under the
uniform measure on a finite `Ω` (`pushLaw`, a counting ratio by `pushLaw_eq_card_div`) is a
distribution, and the law of a product of independent samples is the convolution of their laws
(`groupConv_pushLaw`).

Fourier transforms `ρ̂(f) = ∑_g f g • ρ g` at a representation `ρ` over `ℂ` (`groupFourier`):
linearity, the convolution theorem `ρ̂(p * q) = ρ̂(p) ρ̂(q)` and its powers, translations, and
`ρ̂(pushLaw P) = |Ω|⁻¹ ∑_ω ρ (P ω)`. The group average `A = |G|⁻¹ ∑_g ρ g` (`groupAverage`) is an
idempotent projection onto the invariants `V^G` that absorbs `ρ̂(p)` for every law `p`, so
`ρ̂(p^{*(t+1)} - u) = (ρ̂(p) - A)^{t+1}`. For an irreducible `ρ` with a non-invariant vector the
average vanishes; on a finite-dimensional irreducible `ρ`, Schur's lemma
(`exists_eq_smul_one_of_commute`) gives `∑_g ρ g T ρ g⁻¹ = (|G| tr T / dim V) • 1`.

Unitary representations (`IsUnitaryRepresentation`, equivalently norm preserving): `ρ g† = ρ g⁻¹`,
`‖ρ̂(f)‖ ≤ ∑ |f g|`, `‖ρ̂(p)‖ ≤ 1` for a law `p`, `ρ̂(f)† = ρ̂(g ↦ conj (f g⁻¹))`, the average is
self-adjoint, and Schur orthogonality `∑_g |⟪u, ρ g v⟫|² = |G| ‖u‖² ‖v‖² / dim V` for irreducible
`ρ` (`sum_norm_inner_sq`).

Hilbert–Schmidt norms `‖A‖²_HS = re tr (A† A)` on a finite-dimensional complex inner product
space (`hilbertSchmidtSq`): the formula `∑ ‖A bᵢ‖²` in any orthonormal basis, `‖A‖² ≤ ‖A‖²_HS ≤
dim V ‖A‖²`, `‖A B‖²_HS ≤ ‖A‖² ‖B‖²_HS` and `≤ ‖A‖²_HS ‖B‖²`, invariance under adjoints, isometries
and unitary `ρ g` on either side, and `‖P‖²_HS = rank P` for a self-adjoint idempotent, so
`‖A‖²_HS = dim V^G` for the average. Singular values: `∑ σᵢ² = ‖A‖²_HS`
(`sum_sq_singularValues`), `σᵢ ≤ ‖A‖` and `∑ σᵢ^p ≤ ‖A‖^(p-2) ‖A‖²_HS` for `p ≥ 2`. The left
regular representation on `ℓ²(G)` (`leftRegular`) is unitary with
`‖ρ̂_reg(f)‖²_HS = |G| ∑ |f g|²`, so `‖p - q‖_TV ≤ ½ ‖ρ̂_reg(p - q)‖_HS`. Subgroup averages
`P_H = |H|⁻¹ ∑_{h ∈ H} ρ h` (`subgroupAverage`) are projections onto `V^H`, self-adjoint for
unitary `ρ` with `‖P_H‖²_HS = dim V^H`, and `ρ̂(f) P_H = ρ̂(f_H)` for the average `f_H` of `f` over
right cosets `g H`.

Sources: P. Diaconis, *Group Representations in Probability and Statistics*, IMS Lecture Notes
11 (1988), ch. 2–3; J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42
(1977), ch. 1–2; A. Terras, *Fourier Analysis on Finite Groups and Applications*, LMS Student
Texts 43 (1999); D. A. Levin and Y. Peres, *Markov Chains and Mixing Times*, 2nd ed., AMS (2017),
ch. 2 and 4 (random walks on groups, submultiplicativity); S. Axler, *Linear Algebra Done Right*,
4th ed. (2024), ch. 7 (singular values); R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed.
(2013), ch. 5. Textbook material; nothing here is specific to a benchmark problem. There is no
Plancherel formula, isotypic decomposition, character table, dimension or degree sum, symmetric
group or Specht module material, and no mixing-time bound for any particular walk.

Bridges: `∑ g, f g • ρ g` is `groupFourier ρ f`, `∑ x, p x * q (x⁻¹ * g)` is `groupConv p q g`,
`if g = 1 then 1 else 0` is `deltaOne g`, `(LinearMap.trace ℂ V (LinearMap.adjoint A * A)).re` is
`hilbertSchmidtSq A` and `∀ g x y, ⟪ρ g x, ρ g y⟫ = ⟪x, y⟫` is `IsUnitaryRepresentation ρ`, all by
`rfl`; `∑ ω, if f ω = g then |Ω|⁻¹ else 0` is `pushLaw f g` by `rfl` and a counting ratio by
`pushLaw_eq_card_div`; a recursion `u 0 = δ₁`, `u (n+1) = p * u n` is `groupConvPow p`
(`eq_groupConvPow`); `∀ g x, ‖ρ g x‖ = ‖x‖` is `isUnitaryRepresentation_iff_norm`; the regular
representation `f ↦ (h ↦ f (g⁻¹ h))` on `EuclideanSpace ℂ G` is `leftRegular G` by `rfl`;
`(1 / ((2 : ℕ) : ℝ)) * ∑ |p - q|` is `tvDist` (`tvDist_eq_natCast_half`).
-/

namespace TheoremOS.RepresentationTheory

noncomputable section

open Finset
open TheoremOS.InformationTheory TheoremOS.Probability
open scoped BigOperators ComplexConjugate InnerProductSpace MonoidAlgebra

section Laws

variable {G : Type*} [Group G] [Fintype G]

/-- Convolution `(p * q)(g) = ∑ₓ p x q (x⁻¹ g)` on a finite group. -/
def groupConv {k : Type*} [Semiring k] (p q : G → k) (g : G) : k := ∑ x, p x * q (x⁻¹ * g)

/-- The point mass at the identity, the unit for `groupConv`. -/
def deltaOne {k : Type*} [Semiring k] (g : G) : k := by
  classical
  exact if g = 1 then 1 else 0

/-- Convolution powers: `p^{*0} = δ₁` and `p^{*(n+1)} = p * p^{*n}`. -/
def groupConvPow {k : Type*} [Semiring k] (p : G → k) : ℕ → G → k
  | 0 => deltaOne
  | n + 1 => groupConv p (groupConvPow p n)

variable {k : Type*} [Semiring k]

theorem groupConv_apply (p q : G → k) (g : G) : groupConv p q g = ∑ x, p x * q (x⁻¹ * g) := rfl

theorem groupConv_apply' (p q : G → k) (g : G) : groupConv p q g = ∑ y, p (g * y⁻¹) * q y := by
  rw [groupConv_apply]
  exact Fintype.sum_equiv ((Equiv.mulLeft g⁻¹).trans (Equiv.inv G)) _ _ fun x => by simp

omit [Fintype G] in
theorem deltaOne_apply [DecidableEq G] (g : G) : (deltaOne g : k) = if g = 1 then 1 else 0 := by
  unfold deltaOne
  congr

theorem sum_groupConv (p q : G → k) : ∑ g, groupConv p q g = (∑ g, p g) * ∑ g, q g := by
  simp only [groupConv_apply]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Fintype.sum_congr _ _ fun x => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun g => by simp

theorem groupConv_assoc (p q r : G → k) :
    groupConv (groupConv p q) r = groupConv p (groupConv q r) := by
  funext g
  simp only [groupConv_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun x => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun y => by simp [mul_assoc]

theorem groupConv_deltaOne (p : G → k) : groupConv p deltaOne = p := by
  classical
  funext g
  simp [groupConv_apply, deltaOne_apply, inv_mul_eq_one, eq_comm]

theorem deltaOne_groupConv (q : G → k) : groupConv deltaOne q = q := by
  classical
  funext g
  simp [groupConv_apply, deltaOne_apply]

theorem groupConv_add_left (p p' q : G → k) :
    groupConv (p + p') q = groupConv p q + groupConv p' q := by
  funext g
  simp [groupConv_apply, add_mul, Finset.sum_add_distrib]

theorem groupConv_add_right (p q q' : G → k) :
    groupConv p (q + q') = groupConv p q + groupConv p q' := by
  funext g
  simp [groupConv_apply, mul_add, Finset.sum_add_distrib]

@[simp] theorem groupConvPow_zero (p : G → k) : groupConvPow p 0 = deltaOne := rfl

theorem groupConvPow_succ (p : G → k) (n : ℕ) :
    groupConvPow p (n + 1) = groupConv p (groupConvPow p n) := rfl

@[simp] theorem groupConvPow_one (p : G → k) : groupConvPow p 1 = p := by
  rw [groupConvPow_succ, groupConvPow_zero, groupConv_deltaOne]

theorem groupConvPow_add (p : G → k) (m n : ℕ) :
    groupConvPow p (m + n) = groupConv (groupConvPow p m) (groupConvPow p n) := by
  induction m with
  | zero => simp [deltaOne_groupConv]
  | succ m ih => rw [Nat.add_right_comm, groupConvPow_succ, ih, groupConvPow_succ, groupConv_assoc]

theorem groupConvPow_succ' (p : G → k) (n : ℕ) :
    groupConvPow p (n + 1) = groupConv (groupConvPow p n) p := by
  rw [groupConvPow_add, groupConvPow_one]

/-- Any sequence with the recursion of `groupConvPow` is `groupConvPow`. -/
theorem eq_groupConvPow {p : G → k} {u : ℕ → G → k} (h0 : u 0 = deltaOne)
    (hs : ∀ n, u (n + 1) = groupConv p (u n)) (n : ℕ) : u n = groupConvPow p n := by
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs, ih, groupConvPow_succ]

theorem sum_groupConvPow (p : G → k) (n : ℕ) : ∑ g, groupConvPow p n g = (∑ g, p g) ^ n := by
  classical
  induction n with
  | zero => simp [deltaOne_apply]
  | succ n ih => rw [groupConvPow_succ, sum_groupConv, ih, pow_succ']

end Laws

section RealLaws

variable {G : Type*} [Group G] [Fintype G]

theorem groupConv_nonneg {p q : G → ℝ} (hp : ∀ g, 0 ≤ p g) (hq : ∀ g, 0 ≤ q g) (g : G) :
    0 ≤ groupConv p q g :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hq _)

theorem isDistribution_groupConv {p q : G → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    IsDistribution (groupConv p q) where
  nonneg := groupConv_nonneg hp.nonneg hq.nonneg
  sum_eq_one := by rw [sum_groupConv, hp.sum_eq_one, hq.sum_eq_one, one_mul]

theorem isDistribution_deltaOne : IsDistribution (deltaOne : G → ℝ) := by
  classical
  refine ⟨fun g => ?_, ?_⟩
  · rw [deltaOne_apply]; split_ifs <;> norm_num
  · simp [deltaOne_apply]

theorem isDistribution_groupConvPow {p : G → ℝ} (hp : IsDistribution p) (n : ℕ) :
    IsDistribution (groupConvPow p n) := by
  induction n with
  | zero => exact isDistribution_deltaOne
  | succ n ih => exact isDistribution_groupConv hp ih

/-- Convolving with the uniform law gives `(∑ p) · uniform`, on either side. -/
theorem groupConv_uniform (p : G → ℝ) : groupConv p (uniform G) = (∑ g, p g) • uniform G := by
  funext g
  simp [groupConv_apply, uniform, Finset.sum_mul]

theorem uniform_groupConv (q : G → ℝ) : groupConv (uniform G) q = (∑ g, q g) • uniform G := by
  funext g
  simp only [groupConv_apply, uniform, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  rw [mul_comm]
  congr 1
  exact Fintype.sum_equiv ((Equiv.mulLeft g⁻¹).trans (Equiv.inv G)) _ _ fun x => by simp

theorem groupConv_uniform_of_isDistribution {p : G → ℝ} (hp : IsDistribution p) :
    groupConv p (uniform G) = uniform G := by
  rw [groupConv_uniform, hp.sum_eq_one, one_smul]

theorem uniform_groupConv_of_isDistribution {q : G → ℝ} (hq : IsDistribution q) :
    groupConv (uniform G) q = uniform G := by
  rw [uniform_groupConv, hq.sum_eq_one, one_smul]

theorem groupConv_sub_left (p p' q : G → ℝ) :
    groupConv (p - p') q = groupConv p q - groupConv p' q := by
  funext g
  simp [groupConv_apply, sub_mul, Finset.sum_sub_distrib]

theorem groupConv_sub_right (p q q' : G → ℝ) :
    groupConv p (q - q') = groupConv p q - groupConv p q' := by
  funext g
  simp [groupConv_apply, mul_sub, Finset.sum_sub_distrib]

/-- `‖p * q‖₁ ≤ ‖p‖₁ ‖q‖₁`. -/
theorem sum_abs_groupConv_le (p q : G → ℝ) :
    ∑ g, |groupConv p q g| ≤ (∑ g, |p g|) * ∑ g, |q g| := by
  calc ∑ g, |groupConv p q g| ≤ ∑ g, groupConv (fun x => |p x|) (fun x => |q x|) g :=
        Finset.sum_le_sum fun g _ => (Finset.abs_sum_le_sum_abs _ _).trans_eq
          (Fintype.sum_congr _ _ fun x => abs_mul _ _)
    _ = (∑ g, |p g|) * ∑ g, |q g| := sum_groupConv _ _

/-- Convolving with a law on the left does not increase total variation. -/
theorem tvDist_groupConv_left_le {r : G → ℝ} (hr : IsDistribution r) (p q : G → ℝ) :
    tvDist (groupConv r p) (groupConv r q) ≤ tvDist p q := by
  have h := sum_abs_groupConv_le r (p - q)
  rw [groupConv_sub_right] at h
  simp only [Pi.sub_apply, abs_of_nonneg (hr.nonneg _), hr.sum_eq_one, one_mul] at h
  simp only [tvDist]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- Convolving with a law on the right does not increase total variation. -/
theorem tvDist_groupConv_right_le {r : G → ℝ} (hr : IsDistribution r) (p q : G → ℝ) :
    tvDist (groupConv p r) (groupConv q r) ≤ tvDist p q := by
  have h := sum_abs_groupConv_le (p - q) r
  rw [groupConv_sub_left] at h
  simp only [Pi.sub_apply, abs_of_nonneg (hr.nonneg _), hr.sum_eq_one, mul_one] at h
  simp only [tvDist]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-- **Submultiplicativity**: `‖p * q - u‖_TV ≤ 2 ‖p - u‖_TV ‖q - u‖_TV` for laws `p`, `q`. -/
theorem tvDist_groupConv_uniform_le {p q : G → ℝ} (hp : IsDistribution p)
    (hq : IsDistribution q) :
    tvDist (groupConv p q) (uniform G) ≤
      2 * tvDist p (uniform G) * tvDist q (uniform G) := by
  have key : groupConv (p - uniform G) (q - uniform G) = groupConv p q - uniform G := by
    rw [groupConv_sub_left, groupConv_sub_right, groupConv_sub_right,
      groupConv_uniform_of_isDistribution hp, uniform_groupConv_of_isDistribution hq,
      groupConv_uniform_of_isDistribution isDistribution_uniform]
    abel
  have h := sum_abs_groupConv_le (p - uniform G) (q - uniform G)
  rw [key] at h
  simp only [Pi.sub_apply] at h
  simp only [tvDist]
  nlinarith

/-- The distance to uniform of `p^{*t}` is nonincreasing in `t`. -/
theorem tvDist_groupConvPow_succ_le {p : G → ℝ} (hp : IsDistribution p) (t : ℕ) :
    tvDist (groupConvPow p (t + 1)) (uniform G) ≤ tvDist (groupConvPow p t) (uniform G) := by
  have h := tvDist_groupConv_left_le hp (groupConvPow p t) (uniform G)
  rwa [← groupConvPow_succ, groupConv_uniform_of_isDistribution hp] at h

/-- `‖p^{*(s+t)} - u‖_TV ≤ 2 ‖p^{*s} - u‖_TV ‖p^{*t} - u‖_TV`. -/
theorem tvDist_groupConvPow_add_le {p : G → ℝ} (hp : IsDistribution p) (s t : ℕ) :
    tvDist (groupConvPow p (s + t)) (uniform G) ≤
      2 * tvDist (groupConvPow p s) (uniform G) * tvDist (groupConvPow p t) (uniform G) := by
  rw [groupConvPow_add]
  exact tvDist_groupConv_uniform_le (isDistribution_groupConvPow hp s)
    (isDistribution_groupConvPow hp t)

end RealLaws

section PushLaw

variable {Ω β : Type*} [Fintype Ω]

/-- The law of `f : Ω → β` under the uniform measure on `Ω`:
`pushLaw f b = ∑_ω [f ω = b] / |Ω|`. -/
def pushLaw (f : Ω → β) (b : β) : ℝ := by
  classical
  exact ∑ ω, if f ω = b then (Fintype.card Ω : ℝ)⁻¹ else 0

theorem pushLaw_apply [DecidableEq β] (f : Ω → β) (b : β) :
    pushLaw f b = ∑ ω, if f ω = b then (Fintype.card Ω : ℝ)⁻¹ else 0 := by
  unfold pushLaw
  exact Finset.sum_congr rfl fun ω _ => by congr

theorem pushLaw_eq_card_div (f : Ω → β) (b : β) [Fintype {ω // f ω = b}] :
    pushLaw f b = (Fintype.card {ω // f ω = b} : ℝ) / Fintype.card Ω := by
  classical
  rw [pushLaw_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, div_eq_mul_inv]
  congr 2
  rw [Fintype.card_subtype]

theorem pushLaw_nonneg (f : Ω → β) (b : β) : 0 ≤ pushLaw f b := by
  classical
  rw [pushLaw_apply]
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> positivity

/-- Expectations against `pushLaw f` are averages over `Ω`, for values in any real vector
space. -/
theorem sum_pushLaw_smul [Fintype β] {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : Ω → β) (A : β → M) :
    ∑ b, pushLaw f b • A b = (Fintype.card Ω : ℝ)⁻¹ • ∑ ω, A (f ω) := by
  classical
  simp only [pushLaw_apply, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Fintype.sum_congr _ _ fun ω => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem sum_pushLaw_mul [Fintype β] (f : Ω → β) (φ : β → ℝ) :
    ∑ b, pushLaw f b * φ b = (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, φ (f ω) :=
  sum_pushLaw_smul f φ

theorem isDistribution_pushLaw [Fintype β] [Nonempty Ω] (f : Ω → β) :
    IsDistribution (pushLaw f) where
  nonneg := pushLaw_nonneg f
  sum_eq_one := by
    have h := sum_pushLaw_mul f (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [h, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- The law of a uniformly random bijection's value is uniform. -/
theorem pushLaw_equiv [Fintype β] (e : Ω ≃ β) : pushLaw e = uniform β := by
  classical
  funext b
  simp [pushLaw_apply, uniform, ← Equiv.eq_symm_apply, Fintype.card_congr e]

/-- The law of a product of independent uniform samples is the convolution of their laws. -/
theorem groupConv_pushLaw {G Ξ : Type*} [Group G] [Fintype G] [Fintype Ξ] (P : Ω → G)
    (Q : Ξ → G) :
    groupConv (pushLaw P) (pushLaw Q) = pushLaw (fun z : Ω × Ξ => P z.1 * Q z.2) := by
  classical
  funext g
  rw [groupConv_apply, sum_pushLaw_mul P (fun x => pushLaw Q (x⁻¹ * g))]
  simp only [pushLaw_apply, Fintype.sum_prod_type, Finset.mul_sum, Fintype.card_prod,
    Nat.cast_mul, mul_inv]
  refine Fintype.sum_congr _ _ fun ω => Fintype.sum_congr _ _ fun ξ => ?_
  have : (Q ξ = (P ω)⁻¹ * g) ↔ (P ω * Q ξ = g) := by
    rw [eq_inv_mul_iff_mul_eq]
  by_cases h : P ω * Q ξ = g <;> simp [this, h]

end PushLaw

section Fourier

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/-- The Fourier transform of `f : G → ℂ` at a representation: `ρ̂(f) = ∑_g f g • ρ g`. -/
def groupFourier (f : G → ℂ) : Module.End ℂ V := ∑ g, f g • ρ g

theorem groupFourier_apply (f : G → ℂ) (v : V) : groupFourier ρ f v = ∑ g, f g • ρ g v := by
  simp [groupFourier, LinearMap.sum_apply]

theorem groupFourier_add (f f' : G → ℂ) :
    groupFourier ρ (f + f') = groupFourier ρ f + groupFourier ρ f' := by
  simp [groupFourier, add_smul, Finset.sum_add_distrib]

theorem groupFourier_sub (f f' : G → ℂ) :
    groupFourier ρ (f - f') = groupFourier ρ f - groupFourier ρ f' := by
  simp [groupFourier, sub_smul, Finset.sum_sub_distrib]

theorem groupFourier_smul (c : ℂ) (f : G → ℂ) :
    groupFourier ρ (c • f) = c • groupFourier ρ f := by
  simp [groupFourier, Finset.smul_sum, smul_smul]

@[simp] theorem groupFourier_zero : groupFourier ρ (0 : G → ℂ) = 0 := by
  simp [groupFourier]

@[simp] theorem groupFourier_deltaOne : groupFourier ρ deltaOne = 1 := by
  classical
  simp [groupFourier, deltaOne_apply]

/-- **Convolution theorem**: `ρ̂(p * q) = ρ̂(p) ρ̂(q)`. -/
theorem groupFourier_groupConv (p q : G → ℂ) :
    groupFourier ρ (groupConv p q) = groupFourier ρ p * groupFourier ρ q := by
  have h : groupFourier ρ p * groupFourier ρ q = ∑ x, ∑ y, (p x * q y) • ρ (x * y) := by
    simp only [groupFourier, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_mul]
    exact Finset.sum_comm
  rw [h, groupFourier]
  simp only [groupConv_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun x => ?_
  exact Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun g => by simp

theorem groupFourier_groupConvPow (p : G → ℂ) (n : ℕ) :
    groupFourier ρ (groupConvPow p n) = groupFourier ρ p ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [groupConvPow_succ, groupFourier_groupConv, ih, pow_succ']

omit [Fintype G] in
theorem ofReal_deltaOne : (fun g => ((deltaOne g : ℝ) : ℂ)) = (deltaOne : G → ℂ) := by
  classical
  funext g
  simp only [deltaOne_apply]
  split_ifs <;> simp

theorem ofReal_groupConv (p q : G → ℝ) :
    (fun g => ((groupConv p q g : ℝ) : ℂ)) =
      groupConv (fun g => (p g : ℂ)) (fun g => (q g : ℂ)) := by
  funext g
  simp [groupConv_apply]

theorem ofReal_groupConvPow (p : G → ℝ) (n : ℕ) :
    (fun g => ((groupConvPow p n g : ℝ) : ℂ)) = groupConvPow (fun g => (p g : ℂ)) n := by
  induction n with
  | zero => exact ofReal_deltaOne
  | succ n ih =>
    rw [groupConvPow_succ, groupConvPow_succ, ofReal_groupConv, ih]

/-- The Fourier transform of the `n`-step law of a random walk with step law `p` is
`ρ̂(p)^n`. -/
theorem groupFourier_ofReal_groupConvPow (p : G → ℝ) (n : ℕ) :
    groupFourier ρ (fun g => ((groupConvPow p n g : ℝ) : ℂ)) =
      groupFourier ρ (fun g => (p g : ℂ)) ^ n := by
  rw [ofReal_groupConvPow, groupFourier_groupConvPow]

theorem groupFourier_ofReal_groupConv (p q : G → ℝ) :
    groupFourier ρ (fun g => ((groupConv p q g : ℝ) : ℂ)) =
      groupFourier ρ (fun g => (p g : ℂ)) * groupFourier ρ (fun g => (q g : ℂ)) := by
  rw [ofReal_groupConv, groupFourier_groupConv]

/-- The Fourier transform of the law of `P : Ω → G` is the average `|Ω|⁻¹ ∑_ω ρ (P ω)`. -/
theorem groupFourier_pushLaw {Ω : Type*} [Fintype Ω] (P : Ω → G) :
    groupFourier ρ (fun g => (pushLaw P g : ℂ)) = (Fintype.card Ω : ℂ)⁻¹ • ∑ ω, ρ (P ω) := by
  classical
  simp only [groupFourier, pushLaw_apply]
  push_cast
  simp only [Finset.sum_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun ω => ?_
  rw [Finset.sum_eq_single (P ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- Translations: `ρ̂(f(a⁻¹ ·)) = ρ a ρ̂(f)` and `ρ̂(f(· a⁻¹)) = ρ̂(f) ρ a`. -/
theorem groupFourier_comp_mul_left (f : G → ℂ) (a : G) :
    groupFourier ρ (fun g => f (a⁻¹ * g)) = ρ a * groupFourier ρ f := by
  simp only [groupFourier, Finset.mul_sum, mul_smul_comm]
  refine Fintype.sum_equiv (Equiv.mulLeft a⁻¹) _ _ fun g => ?_
  simp [← map_mul]

theorem groupFourier_comp_mul_right (f : G → ℂ) (a : G) :
    groupFourier ρ (fun g => f (g * a⁻¹)) = groupFourier ρ f * ρ a := by
  simp only [groupFourier, Finset.sum_mul, smul_mul_assoc]
  refine Fintype.sum_equiv (Equiv.mulRight a⁻¹) _ _ fun g => ?_
  simp [← map_mul]

/-- The group average `|G|⁻¹ ∑_g ρ g`, the Fourier transform of the uniform law. -/
def groupAverage : Module.End ℂ V := (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g

theorem groupFourier_uniform :
    groupFourier ρ (fun g => (uniform G g : ℂ)) = groupAverage ρ := by
  simp [groupFourier, groupAverage, uniform, Finset.smul_sum]

theorem groupFourier_const (c : ℂ) : groupFourier ρ (fun _ => c) = c • ∑ g, ρ g := by
  simp [groupFourier, Finset.smul_sum]

theorem mul_groupAverage (h : G) : ρ h * groupAverage ρ = groupAverage ρ := by
  simp only [groupAverage, mul_smul_comm, Finset.mul_sum, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => rfl

theorem groupAverage_mul (h : G) : groupAverage ρ * ρ h = groupAverage ρ := by
  simp only [groupAverage, smul_mul_assoc, Finset.sum_mul, ← map_mul]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => rfl

theorem groupAverage_mul_groupAverage : groupAverage ρ * groupAverage ρ = groupAverage ρ := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc groupAverage ρ * groupAverage ρ
      = (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g * groupAverage ρ := by
        rw [groupAverage, smul_mul_assoc, Finset.sum_mul]
    _ = groupAverage ρ := by
        simp only [mul_groupAverage, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
          smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem groupAverage_apply_mem_invariants (v : V) : groupAverage ρ v ∈ ρ.invariants := by
  intro g
  rw [← Module.End.mul_apply, mul_groupAverage]

theorem groupAverage_apply_of_mem_invariants {v : V} (hv : v ∈ ρ.invariants) :
    groupAverage ρ v = v := by
  rw [Representation.mem_invariants] at hv
  simp [groupAverage, LinearMap.sum_apply, hv, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]

theorem isProj_groupAverage : LinearMap.IsProj ρ.invariants (groupAverage ρ) :=
  ⟨groupAverage_apply_mem_invariants ρ, fun _ => groupAverage_apply_of_mem_invariants ρ⟩

/-- For a law `p`, `ρ̂(p)` and the group average absorb each other. -/
theorem groupFourier_mul_groupAverage {p : G → ℂ} (hp : ∑ g, p g = 1) :
    groupFourier ρ p * groupAverage ρ = groupAverage ρ := by
  simp only [groupFourier, Finset.sum_mul, smul_mul_assoc, mul_groupAverage, ← Finset.sum_smul,
    hp, one_smul]

theorem groupAverage_mul_groupFourier {p : G → ℂ} (hp : ∑ g, p g = 1) :
    groupAverage ρ * groupFourier ρ p = groupAverage ρ := by
  simp only [groupFourier, Finset.mul_sum, mul_smul_comm, groupAverage_mul, ← Finset.sum_smul,
    hp, one_smul]

/-- `ρ̂(p^{*t} - u) = (ρ̂(p) - ρ̂(u))^t` for a law `p` and `t ≥ 1`. -/
theorem groupFourier_groupConvPow_sub_uniform {p : G → ℝ} (hp : ∑ g, p g = 1) (t : ℕ) :
    groupFourier ρ (fun g => ((groupConvPow p (t + 1) g - uniform G g : ℝ) : ℂ)) =
      (groupFourier ρ (fun g => (p g : ℂ)) - groupAverage ρ) ^ (t + 1) := by
  have hp' : ∑ g, (p g : ℂ) = 1 := by exact_mod_cast hp
  set F := groupFourier ρ (fun g => (p g : ℂ))
  set A := groupAverage ρ
  have hFA : F * A = A := groupFourier_mul_groupAverage ρ hp'
  have hAF : A * F = A := groupAverage_mul_groupFourier ρ hp'
  have hAA : A * A = A := groupAverage_mul_groupAverage ρ
  have hpow : ∀ n : ℕ, F ^ n * A = A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, hFA, ih]
  have key : ∀ n : ℕ, (F - A) ^ (n + 1) = F ^ (n + 1) - A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ (F - A) (n + 1), ih, sub_mul, mul_sub, mul_sub, hpow, hAF, hAA, ← pow_succ]
      abel
  have hfun : (fun g => ((groupConvPow p (t + 1) g - uniform G g : ℝ) : ℂ)) =
      (fun g => ((groupConvPow p (t + 1) g : ℝ) : ℂ)) - fun g => ((uniform G g : ℝ) : ℂ) := by
    funext g
    simp
  rw [hfun, groupFourier_sub, groupFourier_ofReal_groupConvPow, groupFourier_uniform, key]

end Fourier

section Irreducible

variable {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

/-- The invariant vectors form a subrepresentation. -/
def invariantsSubrep : Subrepresentation ρ where
  toSubmodule := ρ.invariants
  apply_mem_toSubmodule g v hv := by
    rw [Representation.mem_invariants] at hv ⊢
    intro h
    rw [hv, hv]

/-- An irreducible representation that moves some vector has no invariant vectors, so its
group average vanishes. -/
theorem groupAverage_eq_zero [ρ.IsIrreducible] (hne : ∃ v, v ∉ ρ.invariants) :
    groupAverage ρ = 0 := by
  obtain ⟨v, hv⟩ := hne
  rcases eq_bot_or_eq_top (invariantsSubrep ρ) with hS | hS
  · ext w
    have hw : groupAverage ρ w ∈ (invariantsSubrep ρ).toSubmodule :=
      groupAverage_apply_mem_invariants ρ w
    rw [hS] at hw
    exact (Submodule.mem_bot ℂ).mp hw
  · exact absurd (show v ∈ (invariantsSubrep ρ).toSubmodule by rw [hS]; trivial) hv

theorem groupFourier_uniform_eq_zero [ρ.IsIrreducible] (hne : ∃ v, v ∉ ρ.invariants) :
    groupFourier ρ (fun g => (uniform G g : ℂ)) = 0 := by
  rw [groupFourier_uniform, groupAverage_eq_zero ρ hne]

omit [Fintype G] in
theorem nontrivial_of_isIrreducible [ρ.IsIrreducible] : Nontrivial V := by
  have : IsSimpleModule ℂ[G] ρ.asModule := inferInstance
  exact IsSimpleModule.nontrivial ℂ[G] ρ.asModule

variable [FiniteDimensional ℂ V]

omit [Fintype G] in
/-- **Schur's lemma** over `ℂ`: an endomorphism commuting with an irreducible representation is
a scalar. -/
theorem exists_eq_smul_one_of_commute [ρ.IsIrreducible] (T : Module.End ℂ V)
    (hT : ∀ g, T * ρ g = ρ g * T) : ∃ c : ℂ, T = c • 1 := by
  let f : Representation.IntertwiningMap ρ ρ := ⟨T, fun g => hT g⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 f
  refine ⟨c, ?_⟩
  have h := congrArg Representation.IntertwiningMap.toLinearMap hc
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at h
  exact h.symm

/-- **Twirling**: `∑_g ρ g T ρ g⁻¹ = (|G| tr T / dim V) • 1` for an irreducible `ρ`. -/
theorem sum_conj_eq_trace_smul [ρ.IsIrreducible] (T : Module.End ℂ V) :
    ∑ g, ρ g * T * ρ g⁻¹ =
      ((Fintype.card G : ℂ) * LinearMap.trace ℂ V T / Module.finrank ℂ V) • 1 := by
  set S := ∑ g, ρ g * T * ρ g⁻¹ with hS
  have hcomm : ∀ h, S * ρ h = ρ h * S := by
    intro h
    simp only [hS, Finset.sum_mul, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_assoc, ← map_mul, mul_inv_rev, inv_inv]
    rw [← mul_assoc (ρ h), ← map_mul, mul_inv_cancel_left]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute ρ S hcomm
  have := nontrivial_of_isIrreducible ρ
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr : LinearMap.trace ℂ V S = Fintype.card G * LinearMap.trace ℂ V T := by
    have h1 : ∀ g, LinearMap.trace ℂ V (ρ g * T * ρ g⁻¹) = LinearMap.trace ℂ V T := by
      intro g
      rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    simp [hS, map_sum, h1, Finset.card_univ]
  rw [hc] at htr ⊢
  rw [map_smul, LinearMap.trace_one, smul_eq_mul] at htr
  congr 1
  field_simp
  linear_combination htr

end Irreducible

section Unitary

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- `ρ` preserves the inner product. -/
def IsUnitaryRepresentation (ρ : Representation ℂ G V) : Prop :=
  ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ

variable {ρ : Representation ℂ G V}

theorem isUnitaryRepresentation_iff_norm :
    IsUnitaryRepresentation ρ ↔ ∀ g x, ‖ρ g x‖ = ‖x‖ := by
  constructor
  · intro h g x
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h]
  · intro h g x y
    let e : V →ₗᵢ[ℂ] V := ⟨ρ g, h g⟩
    exact e.inner_map_map x y

namespace IsUnitaryRepresentation

theorem norm_apply (hρ : IsUnitaryRepresentation ρ) (g : G) (x : V) : ‖ρ g x‖ = ‖x‖ :=
  isUnitaryRepresentation_iff_norm.mp hρ g x

theorem inner_inv_apply (hρ : IsUnitaryRepresentation ρ) (g : G) (x y : V) :
    ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
  rw [← hρ g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem restrict (hρ : IsUnitaryRepresentation ρ) (H : Subgroup G) :
    IsUnitaryRepresentation (ρ.comp H.subtype) := fun h x y => hρ h x y

variable [FiniteDimensional ℂ V]

theorem adjoint_eq (hρ : IsUnitaryRepresentation ρ) (g : G) :
    LinearMap.adjoint (ρ g) = ρ g⁻¹ :=
  ((LinearMap.eq_adjoint_iff (ρ g⁻¹) (ρ g)).mpr (hρ.inner_inv_apply g)).symm

theorem opNorm_le_one (hρ : IsUnitaryRepresentation ρ) (g : G) :
    ‖LinearMap.toContinuousLinearMap (ρ g)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simp [hρ.norm_apply g x]

end IsUnitaryRepresentation

variable [Fintype G]

theorem norm_groupFourier_apply_le (hρ : IsUnitaryRepresentation ρ) (f : G → ℂ) (v : V) :
    ‖groupFourier ρ f v‖ ≤ (∑ g, ‖f g‖) * ‖v‖ := by
  rw [groupFourier_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g _ => ?_)
  rw [norm_smul, hρ.norm_apply]

variable [FiniteDimensional ℂ V]

/-- `‖ρ̂(f)‖ ≤ ∑_g |f g|` for a unitary `ρ`. -/
theorem opNorm_groupFourier_le (hρ : IsUnitaryRepresentation ρ) (f : G → ℂ) :
    ‖LinearMap.toContinuousLinearMap (groupFourier ρ f)‖ ≤ ∑ g, ‖f g‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => by
    simpa using norm_groupFourier_apply_le hρ f v

/-- The Fourier transform of a law at a unitary representation is a contraction. -/
theorem opNorm_groupFourier_le_one (hρ : IsUnitaryRepresentation ρ) {p : G → ℝ}
    (hp : IsDistribution p) :
    ‖LinearMap.toContinuousLinearMap (groupFourier ρ (fun g => (p g : ℂ)))‖ ≤ 1 := by
  refine (opNorm_groupFourier_le hρ _).trans_eq ?_
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg _), hp.sum_eq_one]

/-- `ρ̂(f)† = ρ̂(g ↦ conj (f g⁻¹))` for a unitary `ρ`. -/
theorem adjoint_groupFourier (hρ : IsUnitaryRepresentation ρ) (f : G → ℂ) :
    LinearMap.adjoint (groupFourier ρ f) = groupFourier ρ (fun g => conj (f g⁻¹)) := by
  simp only [groupFourier, map_sum, LinearEquiv.map_smulₛₗ, hρ.adjoint_eq]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ fun g => by simp

/-- The group average of a unitary representation is self-adjoint. -/
theorem adjoint_groupAverage (hρ : IsUnitaryRepresentation ρ) :
    LinearMap.adjoint (groupAverage ρ) = groupAverage ρ := by
  rw [← groupFourier_uniform, adjoint_groupFourier hρ]
  congr 1
  funext g
  simp [uniform]

/-- `sampleOperator`-style averages `|Ω|⁻¹ ∑_ω ρ (P ω)` as continuous linear maps. -/
theorem toContinuousLinearMap_groupFourier_pushLaw {Ω : Type*} [Fintype Ω] (P : Ω → G) :
    LinearMap.toContinuousLinearMap (groupFourier ρ (fun g => (pushLaw P g : ℂ))) =
      (Fintype.card Ω : ℂ)⁻¹ • ∑ ω, LinearMap.toContinuousLinearMap (ρ (P ω)) := by
  rw [groupFourier_pushLaw, map_smul, map_sum]

/-- **Schur orthogonality**: `∑_g |⟪u, ρ g v⟫|² = |G| ‖u‖² ‖v‖² / dim V` for an irreducible
unitary `ρ`. -/
theorem sum_norm_inner_sq [ρ.IsIrreducible] (hρ : IsUnitaryRepresentation ρ) (u v : V) :
    ∑ g, ‖⟪u, ρ g v⟫_ℂ‖ ^ 2 =
      Fintype.card G * ‖u‖ ^ 2 * ‖v‖ ^ 2 / Module.finrank ℂ V := by
  let T : Module.End ℂ V := (innerₛₗ ℂ v).smulRight v
  have hT : ∀ x, T x = ⟪v, x⟫_ℂ • v := fun x => rfl
  have hconj : ∀ g x, (ρ g * T * ρ g⁻¹) x = ⟪ρ g v, x⟫_ℂ • ρ g v := by
    intro g x
    simp only [Module.End.mul_apply, hT, map_smul, ← hρ.inner_inv_apply, inv_inv]
  have hself : ∀ w : V, ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := fun w => by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have htr : LinearMap.trace ℂ V T = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [LinearMap.trace_smulRight, innerₛₗ_apply_apply, hself]
  have h := congrArg (fun A : Module.End ℂ V => ⟪u, A u⟫_ℂ) (sum_conj_eq_trace_smul ρ T)
  simp only [LinearMap.sum_apply, inner_sum, hconj, inner_smul_right, LinearMap.smul_apply,
    Module.End.one_apply, htr, hself] at h
  have hterm : ∀ g, ⟪ρ g v, u⟫_ℂ * ⟪u, ρ g v⟫_ℂ = ((‖⟪u, ρ g v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [← inner_conj_symm, Complex.conj_mul']
    push_cast
    ring
  simp only [hterm] at h
  have h' : ((∑ g, ‖⟪u, ρ g v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) =
      ((Fintype.card G * ‖u‖ ^ 2 * ‖v‖ ^ 2 / Module.finrank ℂ V : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h]
    push_cast
    ring
  exact_mod_cast h'

end Unitary

section HilbertSchmidt

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- The squared Hilbert–Schmidt norm `re tr (A† A) = ∑_i ‖A bᵢ‖²`. -/
def hilbertSchmidtSq (A : Module.End ℂ V) : ℝ := (LinearMap.trace ℂ V (LinearMap.adjoint A * A)).re

theorem hilbertSchmidtSq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ V)
    (A : Module.End ℂ V) : hilbertSchmidtSq A = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [hilbertSchmidtSq, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hilbertSchmidtSq_nonneg (A : Module.End ℂ V) : 0 ≤ hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V)]
  positivity

theorem hilbertSchmidtSq_eq_zero_iff (A : Module.End ℂ V) : hilbertSchmidtSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    rw [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V),
      Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h
    exact (stdOrthonormalBasis ℂ V).toBasis.ext fun i => by
      simpa using h i (Finset.mem_univ i)
  · rintro rfl
    simp [hilbertSchmidtSq]

theorem hilbertSchmidtSq_smul (c : ℂ) (A : Module.End ℂ V) :
    hilbertSchmidtSq (c • A) = ‖c‖ ^ 2 * hilbertSchmidtSq A := by
  simp only [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V), LinearMap.smul_apply, norm_smul,
    mul_pow, Finset.mul_sum]

@[simp] theorem hilbertSchmidtSq_one : hilbertSchmidtSq (1 : Module.End ℂ V) = Module.finrank ℂ V := by
  rw [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V)]
  simp [(stdOrthonormalBasis ℂ V).orthonormal.1, Finset.card_univ,
    ← Module.finrank_eq_card_basis (stdOrthonormalBasis ℂ V).toBasis]

theorem hilbertSchmidtSq_adjoint (A : Module.End ℂ V) :
    hilbertSchmidtSq (LinearMap.adjoint A) = hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq, hilbertSchmidtSq, LinearMap.adjoint_adjoint, LinearMap.trace_mul_comm]

/-- `‖A x‖² ≤ ‖A‖²_HS ‖x‖²`. -/
theorem norm_apply_sq_le (A : Module.End ℂ V) (x : V) :
    ‖A x‖ ^ 2 ≤ hilbertSchmidtSq A * ‖x‖ ^ 2 := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  set y := (‖x‖ : ℂ)⁻¹ • x
  have hxn : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖y‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxn,
      inv_mul_cancel₀ hxn.ne']
  have hon : Orthonormal ℂ ((↑) : ({y} : Set V) → V) := by
    rw [orthonormal_subtype_iff_ite]
    rintro a rfl b rfl
    simp [inner_self_eq_norm_sq_to_K, hy]
  obtain ⟨u, b, hyu, hb⟩ := hon.exists_orthonormalBasis_extension
  have hmem : y ∈ u := hyu rfl
  have h1 : ‖A y‖ ^ 2 ≤ hilbertSchmidtSq A := by
    rw [hilbertSchmidtSq_eq_sum b]
    refine le_of_eq_of_le ?_ (Finset.single_le_sum (fun i _ => sq_nonneg ‖A (b i)‖)
      (Finset.mem_univ ⟨y, hmem⟩))
    rw [hb]
  have hAy : A x = (‖x‖ : ℂ) • A y := by
    rw [← map_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hxn.ne'), one_smul]
  rw [hAy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxn, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The operator norm is at most the Hilbert–Schmidt norm. -/
theorem opNorm_sq_le_hilbertSchmidtSq (A : Module.End ℂ V) :
    ‖LinearMap.toContinuousLinearMap A‖ ^ 2 ≤ hilbertSchmidtSq A := by
  have hb : ‖LinearMap.toContinuousLinearMap A‖ ≤ √(hilbertSchmidtSq A) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => by
      rw [LinearMap.coe_toContinuousLinearMap', ← Real.sqrt_sq (norm_nonneg (A x)),
        ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (hilbertSchmidtSq_nonneg A)]
      exact Real.sqrt_le_sqrt (norm_apply_sq_le A x)
  calc ‖LinearMap.toContinuousLinearMap A‖ ^ 2 ≤ √(hilbertSchmidtSq A) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = hilbertSchmidtSq A := Real.sq_sqrt (hilbertSchmidtSq_nonneg A)

theorem hilbertSchmidtSq_le_finrank_mul (A : Module.End ℂ V) :
    hilbertSchmidtSq A ≤ Module.finrank ℂ V * ‖LinearMap.toContinuousLinearMap A‖ ^ 2 := by
  rw [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V)]
  calc ∑ i, ‖A ((stdOrthonormalBasis ℂ V) i)‖ ^ 2
      ≤ ∑ _i : Fin (Module.finrank ℂ V), ‖LinearMap.toContinuousLinearMap A‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := (LinearMap.toContinuousLinearMap A).le_opNorm ((stdOrthonormalBasis ℂ V) i)
        rw [(stdOrthonormalBasis ℂ V).orthonormal.1 i, mul_one] at h
        exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Module.finrank ℂ V * ‖LinearMap.toContinuousLinearMap A‖ ^ 2 := by simp

/-- `‖A B‖²_HS ≤ ‖A‖² ‖B‖²_HS` and `‖A B‖²_HS ≤ ‖A‖²_HS ‖B‖²`. -/
theorem hilbertSchmidtSq_mul_le_left (A B : Module.End ℂ V) :
    hilbertSchmidtSq (A * B) ≤ ‖LinearMap.toContinuousLinearMap A‖ ^ 2 * hilbertSchmidtSq B := by
  simp only [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V), Module.End.mul_apply,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((LinearMap.toContinuousLinearMap A).le_opNorm (B ((stdOrthonormalBasis ℂ V) i))) 2

theorem hilbertSchmidtSq_mul_le_right (A B : Module.End ℂ V) :
    hilbertSchmidtSq (A * B) ≤ hilbertSchmidtSq A * ‖LinearMap.toContinuousLinearMap B‖ ^ 2 := by
  have h := hilbertSchmidtSq_mul_le_left (LinearMap.adjoint B) (LinearMap.adjoint A)
  have hadj : LinearMap.adjoint B * LinearMap.adjoint A = LinearMap.adjoint (A * B) :=
    (LinearMap.adjoint_comp A B).symm
  have := FiniteDimensional.complete ℂ V
  have hn : ‖LinearMap.toContinuousLinearMap (LinearMap.adjoint B)‖ =
      ‖LinearMap.toContinuousLinearMap B‖ := by
    rw [LinearMap.adjoint_toContinuousLinearMap, LinearIsometryEquiv.norm_map]
  rw [hadj, hilbertSchmidtSq_adjoint, hilbertSchmidtSq_adjoint, hn] at h
  linarith

theorem hilbertSchmidtSq_mul_of_norm_map (U A : Module.End ℂ V) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    hilbertSchmidtSq (U * A) = hilbertSchmidtSq A := by
  simp only [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V), Module.End.mul_apply, hU]

/-- Right multiplication by a linear isometry preserves the Hilbert–Schmidt norm. -/
theorem hilbertSchmidtSq_mul_isometry (A : Module.End ℂ V) (U : V ≃ₗᵢ[ℂ] V) :
    hilbertSchmidtSq (A * (U : V →ₗ[ℂ] V)) = hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq_eq_sum (stdOrthonormalBasis ℂ V),
    hilbertSchmidtSq_eq_sum ((stdOrthonormalBasis ℂ V).map U)]
  simp

/-- The Hilbert–Schmidt norm of a self-adjoint idempotent is the dimension of its range. -/
theorem hilbertSchmidtSq_of_isIdempotentElem {P : Module.End ℂ V} (hP : IsIdempotentElem P)
    (hsa : LinearMap.adjoint P = P) :
    hilbertSchmidtSq P = Module.finrank ℂ (LinearMap.range P) := by
  rw [hilbertSchmidtSq, hsa, hP.eq, (LinearMap.IsIdempotentElem.isProj_range P hP).trace]
  simp

/-- `∑ σᵢ² = ‖A‖²_HS`. -/
theorem sum_sq_singularValues (A : Module.End ℂ V) :
    ∑ i : Fin (Module.finrank ℂ V), A.singularValues i ^ 2 = hilbertSchmidtSq A := by
  rw [hilbertSchmidtSq]
  simp only [A.sq_singularValues_fin rfl]
  exact (A.isSymmetric_adjoint_comp_self.re_trace_eq_sum_eigenvalues rfl).symm

theorem singularValues_le_opNorm (A : Module.End ℂ V) (i : ℕ) :
    A.singularValues i ≤ ‖LinearMap.toContinuousLinearMap A‖ := by
  rcases lt_or_ge i (Module.finrank ℂ V) with hi | hi
  · obtain ⟨v, hv⟩ := (A.hasEigenvalue_adjoint_comp_self_sq_singularValues hi).exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hAv : A.singularValues i ^ 2 * ‖v‖ ^ 2 = ‖A v‖ ^ 2 := by
      have h1 := hv.apply_eq_smul
      have h2 : ⟪v, (LinearMap.adjoint A ∘ₗ A) v⟫_ℂ = ⟪A v, A v⟫_ℂ := by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
      rw [h1, inner_smul_right, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
      exact_mod_cast h2
    have hle : A.singularValues i ^ 2 * ‖v‖ ^ 2 ≤ ‖LinearMap.toContinuousLinearMap A‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [hAv, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) ((LinearMap.toContinuousLinearMap A).le_opNorm v) 2
    have hsq := le_of_mul_le_mul_right hle (by positivity)
    exact (pow_le_pow_iff_left₀ (A.singularValues_nonneg i) (norm_nonneg _) two_ne_zero).mp hsq
  · rw [A.singularValues_of_finrank_le hi]
    exact norm_nonneg _

/-- Schatten moments of order `p ≥ 2` are controlled by the operator norm and the
Hilbert–Schmidt norm: `∑ σᵢ^p ≤ ‖A‖^(p-2) ‖A‖²_HS`. -/
theorem sum_singularValues_rpow_le (A : Module.End ℂ V) {p : ℝ} (hp : 2 ≤ p) :
    ∑ i : Fin (Module.finrank ℂ V), A.singularValues i ^ p ≤
      ‖LinearMap.toContinuousLinearMap A‖ ^ (p - 2) * hilbertSchmidtSq A := by
  rw [← sum_sq_singularValues, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 := A.singularValues_nonneg i
  have hsplit : A.singularValues i ^ p = A.singularValues i ^ (p - 2) * A.singularValues i ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add' h0 (by norm_num; linarith)]
    norm_num
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow h0 (singularValues_le_opNorm A i) (by linarith)) (sq_nonneg _)

end HilbertSchmidt

section GroupHilbertSchmidt

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {ρ : Representation ℂ G V}

omit [Fintype G] in
theorem hilbertSchmidtSq_rep_mul (hρ : IsUnitaryRepresentation ρ) (g : G) (A : Module.End ℂ V) :
    hilbertSchmidtSq (ρ g * A) = hilbertSchmidtSq A :=
  hilbertSchmidtSq_mul_of_norm_map _ _ (hρ.norm_apply g)

omit [Fintype G] in
theorem hilbertSchmidtSq_mul_rep (hρ : IsUnitaryRepresentation ρ) (g : G) (A : Module.End ℂ V) :
    hilbertSchmidtSq (A * ρ g) = hilbertSchmidtSq A := by
  have h : LinearMap.adjoint (A * ρ g) = ρ g⁻¹ * LinearMap.adjoint A := by
    rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hρ.adjoint_eq, Module.End.mul_eq_comp]
  rw [← hilbertSchmidtSq_adjoint, h, hilbertSchmidtSq_rep_mul hρ, hilbertSchmidtSq_adjoint]

omit [FiniteDimensional ℂ V] in
theorem range_groupAverage : LinearMap.range (groupAverage ρ) = ρ.invariants := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact groupAverage_apply_mem_invariants ρ v
  · intro v hv
    exact ⟨v, groupAverage_apply_of_mem_invariants ρ hv⟩

/-- `‖|G|⁻¹ ∑_g ρ g‖²_HS = dim V^G`. -/
theorem hilbertSchmidtSq_groupAverage (hρ : IsUnitaryRepresentation ρ) :
    hilbertSchmidtSq (groupAverage ρ) = Module.finrank ℂ ρ.invariants := by
  rw [hilbertSchmidtSq_of_isIdempotentElem (groupAverage_mul_groupAverage ρ)
    (adjoint_groupAverage hρ), range_groupAverage]

end GroupHilbertSchmidt

section LeftRegular

variable (G : Type*) [Group G] [Fintype G]

/-- The left regular representation of `G` on `ℓ²(G)`: `(g • f) h = f (g⁻¹ h)`. -/
def leftRegular : Representation ℂ G (EuclideanSpace ℂ G) where
  toFun g :=
    { toFun := fun f => WithLp.toLp 2 (fun h => f (g⁻¹ * h))
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext f h; simp
  map_mul' := by
    intro x y
    ext f h
    change f ((x * y)⁻¹ * h) = f (y⁻¹ * (x⁻¹ * h))
    simp [mul_assoc]

variable {G}

omit [Fintype G] in
@[simp] theorem leftRegular_apply (g : G) (f : EuclideanSpace ℂ G) (h : G) :
    leftRegular G g f h = f (g⁻¹ * h) := rfl

theorem isUnitaryRepresentation_leftRegular : IsUnitaryRepresentation (leftRegular G) := by
  rw [isUnitaryRepresentation_iff_norm]
  intro g f
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => by simp

theorem groupFourier_leftRegular_single [DecidableEq G] (f : G → ℂ) (x h : G) :
    groupFourier (leftRegular G) f (EuclideanSpace.single x 1) h = f (h * x⁻¹) := by
  classical
  have hc : ∀ b : G, (b⁻¹ * h = x) ↔ (b = h * x⁻¹) := fun b => by
    rw [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq, eq_comm]
  rw [groupFourier_apply]
  simp [hc]

/-- On the regular representation, `‖ρ̂(f)‖²_HS = |G| ∑_g |f g|²`. -/
theorem hilbertSchmidtSq_groupFourier_leftRegular (f : G → ℂ) :
    hilbertSchmidtSq (groupFourier (leftRegular G) f) = Fintype.card G * ∑ g, ‖f g‖ ^ 2 := by
  classical
  rw [hilbertSchmidtSq_eq_sum (EuclideanSpace.basisFun G ℂ)]
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.norm_sq_eq,
    groupFourier_leftRegular_single]
  rw [Finset.sum_congr rfl fun x _ =>
    Fintype.sum_equiv (Equiv.mulRight x⁻¹) (fun h => ‖f (h * x⁻¹)‖ ^ 2) (fun g => ‖f g‖ ^ 2)
      fun h => rfl]
  simp

/-- `‖p - q‖_TV ≤ ½ ‖ρ̂_reg(p - q)‖_HS`. -/
theorem tvDist_le_sqrt_hilbertSchmidtSq (p q : G → ℝ) :
    tvDist p q ≤ (1 / 2 : ℝ) *
      √(hilbertSchmidtSq (groupFourier (leftRegular G) (fun g => ((p g - q g : ℝ) : ℂ)))) := by
  rw [hilbertSchmidtSq_groupFourier_leftRegular, Real.sqrt_mul (Nat.cast_nonneg _)]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h := tvDist_le_sqrt_card_mul p q
  rw [mul_assoc] at h
  exact h

end LeftRegular

section SubgroupAverage

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (H : Subgroup G) [Fintype H]

/-- The average `|H|⁻¹ ∑_{h ∈ H} ρ h` over a subgroup: the projection onto `V^H`. -/
def subgroupAverage : Module.End ℂ V := groupAverage (ρ.comp H.subtype)

theorem subgroupAverage_eq : subgroupAverage ρ H = (Fintype.card H : ℂ)⁻¹ • ∑ h : H, ρ h := rfl

theorem subgroupAverage_mul_subgroupAverage :
    subgroupAverage ρ H * subgroupAverage ρ H = subgroupAverage ρ H :=
  groupAverage_mul_groupAverage _

theorem rep_mul_subgroupAverage {h : G} (hh : h ∈ H) :
    ρ h * subgroupAverage ρ H = subgroupAverage ρ H :=
  mul_groupAverage (ρ.comp H.subtype) ⟨h, hh⟩

theorem subgroupAverage_mul_rep {h : G} (hh : h ∈ H) :
    subgroupAverage ρ H * ρ h = subgroupAverage ρ H :=
  groupAverage_mul (ρ.comp H.subtype) ⟨h, hh⟩

theorem subgroupAverage_apply_mem {v : V} {h : G} (hh : h ∈ H) :
    ρ h (subgroupAverage ρ H v) = subgroupAverage ρ H v := by
  rw [← Module.End.mul_apply, rep_mul_subgroupAverage ρ H hh]

theorem subgroupAverage_apply_of_forall {v : V} (hv : ∀ h ∈ H, ρ h v = v) :
    subgroupAverage ρ H v = v :=
  groupAverage_apply_of_mem_invariants (ρ.comp H.subtype) fun h => hv h h.2

/-- `ρ̂(f) P_H = ρ̂(f_H)` where `f_H g = |H|⁻¹ ∑_{h ∈ H} f (g h)` averages `f` over the right
coset `g H`. -/
theorem groupFourier_mul_subgroupAverage [Fintype G] (f : G → ℂ) :
    groupFourier ρ f * subgroupAverage ρ H =
      groupFourier ρ (fun g => (Fintype.card H : ℂ)⁻¹ * ∑ h : H, f (g * h)) := by
  rw [subgroupAverage_eq, mul_smul_comm, Finset.mul_sum]
  simp only [← groupFourier_comp_mul_right]
  simp only [groupFourier, Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun g => ?_
  exact Fintype.sum_equiv (Equiv.inv H) _ _ fun h => by simp

end SubgroupAverage

section SubgroupAverageUnitary

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] {ρ : Representation ℂ G V} (H : Subgroup G) [Fintype H]

theorem adjoint_subgroupAverage (hρ : IsUnitaryRepresentation ρ) :
    LinearMap.adjoint (subgroupAverage ρ H) = subgroupAverage ρ H :=
  adjoint_groupAverage (hρ.restrict H)

/-- `‖P_H‖²_HS = dim V^H`. -/
theorem hilbertSchmidtSq_subgroupAverage (hρ : IsUnitaryRepresentation ρ) :
    hilbertSchmidtSq (subgroupAverage ρ H) = Module.finrank ℂ (Representation.invariants (ρ.comp H.subtype)) :=
  hilbertSchmidtSq_groupAverage (hρ.restrict H)

end SubgroupAverageUnitary

end

end TheoremOS.RepresentationTheory
