import Mathlib
import Submission.Library.TheoremOS.RepresentationTheory.GroupFourier

/-!
# Plancherel theory for finite groups: Schur orthogonality, complete families and the upper bound lemma

Twirling `T ↦ ∑_g σ g T ρ g⁻¹` (`twirl`) produces intertwining maps and vanishes between
inequivalent irreducibles. Matrix coefficients `g ↦ ⟪ρ g v, u⟫` in `ℓ²(G)` (`matrixCoeff`)
satisfy `⟪c(u, v), f⟫ = ⟪u, ρ̂(f) v⟫`, so `‖ρ̂(f)‖²_HS` is the sum of `|⟪c(eₐ, e_b), f⟫|²` over an
orthonormal basis. Schur orthogonality for unitary irreducibles: `⟪c(u, v), c(u', v')⟫ =
(|G| / dim V) ⟪u, u'⟫ ⟪v', v⟫` and `0` across inequivalent ones. For a pairwise inequivalent
family (`PairwiseInequivalent`) of irreducible unitary representations the normalized
coefficients `√(dᵢ / |G|) c(eₐ, e_b)` (`normalizedCoeff`) are orthonormal, giving Bessel's
inequality `∑ᵢ dᵢ ‖ρ̂ᵢ(f)‖²_HS ≤ |G| ∑_g |f g|²` and the degree bounds `∑ᵢ dᵢ² ≤ |G|` and
`d² ≤ |G|`.

A complete family (`IsCompleteFamily`: irreducible, unitary, pairwise inequivalent, `∑ᵢ dᵢ² =
|G|`) has an orthonormal basis of normalized coefficients, hence the Plancherel formula
`∑ᵢ dᵢ ‖ρ̂ᵢ(f)‖²_HS = |G| ∑_g |f g|²`, Fourier inversion `f x = ∑ᵢ (dᵢ / |G|) tr (ρᵢ(x⁻¹) ρ̂ᵢ(f))`,
uniqueness (`groupFourier_injective`), and every irreducible unitary representation is
equivalent to a member (`exists_equiv`). Existence: `ℓ²(G)` contains a complete family of
irreducible subrepresentations (`exists_isCompleteFamily_subrep`), built by adding a minimal
nonzero invariant subspace of the common kernel of the `ρ̂ᵢ` (nonzero while `∑ dᵢ² < |G|`), which
is irreducible and inequivalent to every `ρᵢ`; with unitary Maschke (orthogonal complements of
invariant subspaces are invariant) every irreducible unitary representation occurs in `ℓ²(G)`.
One-dimensional representations are irreducible.

Upper bound lemma (Diaconis–Shahshahani): `ρ̂(p - u) = ρ̂(p) - P` with `P` the group average,
`‖ρ̂(p) - P‖²_HS = ‖ρ̂(p)‖²_HS - dim V^G` for a law `p`, `|G| ∑_g (p g - u g)² = ∑ᵢ dᵢ ‖ρ̂ᵢ(p) -
Pᵢ‖²_HS`, so `4 ‖p - u‖²_TV ≤ ∑ᵢ dᵢ ‖ρ̂ᵢ(p) - Pᵢ‖²_HS`, `≤ ∑_{i ∈ s} dᵢ ‖ρ̂ᵢ(p)‖²_HS` when the
blocks outside `s` are trivial, and `4 ‖p^{*t} - u‖²_TV ≤ ∑_{i ∈ s} dᵢ² ‖ρ̂ᵢ(p)‖^{2t}` (from
`‖A^t‖²_HS ≤ dim V ‖A‖^{2t}`). For a class function `f` (`IsClassFunction`) `ρ̂(f)` commutes with
`ρ`, and at an irreducible `ρ̂(f) = ((∑_g f g χ_ρ(g)) / dim V) • 1`, so for a conjugation-invariant
step law `4 ‖p^{*t} - u‖²_TV ≤ ∑_{i ∈ s} dᵢ² |(∑_g p g χᵢ(g)) / dᵢ|^{2t}`.

Sources: J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977),
ch. 1–2 and 6 (Schur's lemma, orthogonality, the regular representation, Fourier inversion);
W. Fulton and J. Harris, *Representation Theory*, Springer GTM 129 (1991), §1–2; P. Diaconis,
*Group Representations in Probability and Statistics*, IMS Lecture Notes 11 (1988), ch. 2–3
(Plancherel, the upper bound lemma); P. Diaconis and M. Shahshahani, Generating a random
permutation with random transpositions, *Z. Wahrsch. Verw. Gebiete* 57 (1981), 159–179, §3
(the upper bound lemma); A. Terras, *Fourier Analysis on Finite Groups and Applications*, LMS
Student Texts 43 (1999), ch. 15–16. Textbook material; nothing here is specific to a benchmark
problem. There is no Specht module, symmetric group, Young diagram or Kronecker coefficient
material, no identification of irreducibles with any concrete family, no count of irreducibles,
no character table, character ratio or degree-sum (Witten zeta) estimate, no Weyl unitarization
of non-unitary representations, and no mixing-time bound for any particular walk.

Bridges: `∀ g x y, ⟪ρ g x, ρ g y⟫ = ⟪x, y⟫` is `IsUnitaryRepresentation ρ`, `g ↦ ⟪ρ g v, u⟫` in
`EuclideanSpace ℂ G` is `matrixCoeff ρ u v`, `∀ g h, f (h * g * h⁻¹) = f g` is
`IsClassFunction f` and `LinearMap.trace ℂ V (ρ g)` is `ρ.character g`, all by `rfl`; a family
of representations on `EuclideanSpace ℂ (Fin (D i))` or on subrepresentation carriers plugs into
`IsCompleteFamily` directly (state `(V := fun i => (W i).toSubmodule)` and
`IsUnitaryRepresentation (V := W.toSubmodule) _` explicitly for subrepresentations, otherwise
elaboration of the normed instances can time out); `‖LinearMap.toContinuousLinearMap
(groupFourier ρ f)‖` is the operator norm used in the random walk bound.
-/

namespace TheoremOS.RepresentationTheory

noncomputable section

open Finset
open TheoremOS.InformationTheory TheoremOS.Probability
open scoped BigOperators ComplexConjugate InnerProductSpace

section Twirl

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

/-- The twirl `∑_g σ g ∘ T ∘ ρ g⁻¹` of a linear map `T : V → W`. -/
def twirl (T : V →ₗ[ℂ] W) : V →ₗ[ℂ] W := ∑ g, σ g ∘ₗ T ∘ₗ ρ g⁻¹

theorem twirl_apply (T : V →ₗ[ℂ] W) (x : V) : twirl ρ σ T x = ∑ g, σ g (T (ρ g⁻¹ x)) := by
  simp [twirl]

theorem twirl_comp (T : V →ₗ[ℂ] W) (h : G) : twirl ρ σ T ∘ₗ ρ h = σ h ∘ₗ twirl ρ σ T := by
  ext x
  simp only [LinearMap.comp_apply, twirl_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply,
    Representation.self_inv_apply]

/-- The twirl as an intertwining map. -/
def twirlIntertwining (T : V →ₗ[ℂ] W) : Representation.IntertwiningMap ρ σ :=
  ⟨twirl ρ σ T, twirl_comp ρ σ T⟩

/-- **Schur's lemma**: twirls between inequivalent irreducible representations vanish. -/
theorem twirl_eq_zero [ρ.IsIrreducible] [σ.IsIrreducible] [IsEmpty (Representation.Equiv ρ σ)]
    (T : V →ₗ[ℂ] W) : twirl ρ σ T = 0 := by
  have h : twirlIntertwining ρ σ T = 0 := Subsingleton.elim _ _
  exact congrArg Representation.IntertwiningMap.toLinearMap h

end Twirl

section MatrixCoefficients

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (ρ : Representation ℂ G V)

/-- The conjugated matrix coefficient `g ↦ ⟪ρ g v, u⟫` as a vector of `ℓ²(G)`. -/
def matrixCoeff (u v : V) : EuclideanSpace ℂ G := WithLp.toLp 2 fun g => ⟪ρ g v, u⟫_ℂ

omit [Fintype G] in
@[simp] theorem matrixCoeff_apply (u v : V) (g : G) : matrixCoeff ρ u v g = ⟪ρ g v, u⟫_ℂ := rfl

/-- Matrix entries of a Fourier transform are `ℓ²(G)` inner products. -/
theorem inner_matrixCoeff (u v : V) (f : EuclideanSpace ℂ G) :
    ⟪matrixCoeff ρ u v, f⟫_ℂ = ⟪u, groupFourier ρ f v⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, groupFourier_apply, inner_sum]
  simp only [dotProduct, inner_smul_right]
  refine Fintype.sum_congr _ _ fun g => ?_
  simp

end MatrixCoefficients

section Schur

variable {G : Type*} [Group G] [Fintype G]
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem inner_matrixCoeff_eq_sum (u v : V) (u' v' : W) :
    ⟪matrixCoeff ρ u v, matrixCoeff σ u' v'⟫_ℂ = ∑ g, ⟪u, ρ g v⟫_ℂ * ⟪σ g v', u'⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, matrixCoeff_apply]
  refine Fintype.sum_congr _ _ fun g => ?_
  simp [mul_comm]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- `∑_g ⟪u, ρ g v⟫ ⟪σ g v', u'⟫ = ⟪u, twirl (⟪v', ·⟫ • v) u'⟫` for unitary `σ`. -/
theorem inner_matrixCoeff_eq_inner_twirl (hσ : IsUnitaryRepresentation σ) (u v : V)
    (u' v' : W) :
    ⟪matrixCoeff ρ u v, matrixCoeff σ u' v'⟫_ℂ =
      ⟪u, twirl σ ρ ((innerₛₗ ℂ v').smulRight v) u'⟫_ℂ := by
  rw [inner_matrixCoeff_eq_sum, twirl_apply, inner_sum]
  refine Fintype.sum_congr _ _ fun g => ?_
  simp only [LinearMap.smulRight_apply, innerₛₗ_apply_apply, map_smul, inner_smul_right]
  rw [← hσ.inner_inv_apply, inv_inv, mul_comm]

/-- **Schur orthogonality** for matrix coefficients of an irreducible unitary representation:
`⟪c(u,v), c(u',v')⟫ = (|G| / dim V) ⟪u,u'⟫ ⟪v',v⟫`. -/
theorem inner_matrixCoeff_self [ρ.IsIrreducible] (hρ : IsUnitaryRepresentation ρ)
    (u v u' v' : V) :
    ⟪matrixCoeff ρ u v, matrixCoeff ρ u' v'⟫_ℂ =
      (Fintype.card G / Module.finrank ℂ V : ℂ) * ⟪u, u'⟫_ℂ * ⟪v', v⟫_ℂ := by
  rw [inner_matrixCoeff_eq_inner_twirl hρ]
  have h := sum_conj_eq_trace_smul ρ ((innerₛₗ ℂ v').smulRight v)
  have ht : twirl ρ ρ ((innerₛₗ ℂ v').smulRight v) = ∑ g, ρ g * (innerₛₗ ℂ v').smulRight v * ρ g⁻¹ :=
    rfl
  rw [ht, h, LinearMap.trace_smulRight, innerₛₗ_apply_apply]
  simp only [LinearMap.smul_apply, Module.End.one_apply, inner_smul_right]
  ring

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- Matrix coefficients of inequivalent irreducible unitary representations are orthogonal. -/
theorem inner_matrixCoeff_eq_zero [ρ.IsIrreducible] [σ.IsIrreducible]
    [IsEmpty (Representation.Equiv σ ρ)] (hσ : IsUnitaryRepresentation σ) (u v : V)
    (u' v' : W) : ⟪matrixCoeff ρ u v, matrixCoeff σ u' v'⟫_ℂ = 0 := by
  rw [inner_matrixCoeff_eq_inner_twirl hσ, twirl_eq_zero, LinearMap.zero_apply, inner_zero_right]

end Schur

section HilbertSchmidtCoeff

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- `‖ρ̂(f)‖²_HS = ∑_{a,b} |⟪c(eₐ, e_b), f⟫|²` in an orthonormal basis `e`. -/
theorem hilbertSchmidtSq_groupFourier_eq_sum (ρ : Representation ℂ G V) {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ V) (f : EuclideanSpace ℂ G) :
    hilbertSchmidtSq (groupFourier ρ f) =
      ∑ a, ∑ b, ‖⟪matrixCoeff ρ (e a) (e b), f⟫_ℂ‖ ^ 2 := by
  rw [hilbertSchmidtSq_eq_sum e, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun b => ?_
  rw [← e.sum_sq_norm_inner_right]
  simp only [inner_matrixCoeff]

end HilbertSchmidtCoeff

section Bessel

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
variable (ρ : ∀ i, Representation ℂ G (V i))

/-- The representations of a family are pairwise inequivalent. -/
def PairwiseInequivalent : Prop := ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (ρ i) (ρ j))

/-- Normalized matrix coefficients `√(dᵢ/|G|) c(eₐ, e_b)` of a family of representations. -/
def normalizedCoeff (k : (i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) :
    EuclideanSpace ℂ G :=
  ((√(Module.finrank ℂ (V k.1) / Fintype.card G : ℝ) : ℝ) : ℂ) •
    matrixCoeff (ρ k.1) (stdOrthonormalBasis ℂ (V k.1) k.2.1) (stdOrthonormalBasis ℂ (V k.1) k.2.2)

variable {ρ}

omit [Fintype ι] in
/-- The normalized matrix coefficients of pairwise inequivalent irreducible unitary
representations are orthonormal in `ℓ²(G)`. -/
theorem orthonormal_normalizedCoeff [∀ i, (ρ i).IsIrreducible]
    (hρ : ∀ i, IsUnitaryRepresentation (ρ i)) (hne : PairwiseInequivalent ρ) :
    Orthonormal ℂ (normalizedCoeff (G := G) ρ) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨i, a, b⟩ ⟨j, a', b'⟩
  simp only [normalizedCoeff, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  by_cases hij : i = j
  · subst hij
    rw [inner_matrixCoeff_self (hρ i), OrthonormalBasis.inner_eq_ite, OrthonormalBasis.inner_eq_ite]
    have := nontrivial_of_isIrreducible (ρ i)
    have hd : (0 : ℝ) < Module.finrank ℂ (V i) := Nat.cast_pos.mpr Module.finrank_pos
    have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
    have hd' : (Module.finrank ℂ (V i) : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hG' : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    set c : ℂ := ((√(Module.finrank ℂ (V i) / Fintype.card G : ℝ) : ℝ) : ℂ) with hc
    have hs : c * c * (Fintype.card G / Module.finrank ℂ (V i) : ℂ) = 1 := by
      rw [hc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
      push_cast
      field_simp
    have hiff : (⟨i, a, b⟩ : (i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i)))
        = ⟨i, a', b'⟩ ↔ a = a' ∧ b' = b := by
      rw [Sigma.mk.inj_iff]
      simp [Prod.ext_iff, eq_comm (a := b')]
    rw [if_congr hiff rfl rfl]
    by_cases ha : a = a' <;> by_cases hb : b' = b <;> simp [ha, hb]
    linear_combination hs
  · have := hne j i (Ne.symm hij)
    rw [inner_matrixCoeff_eq_zero (hρ j)]
    have hk : (⟨i, a, b⟩ : (i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i)))
        ≠ ⟨j, a', b'⟩ := fun h => hij (congrArg Sigma.fst h)
    simp [hk]

/-- `∑_k |⟪c̃_k, f⟫|² = |G|⁻¹ ∑_i dᵢ ‖ρ̂ᵢ(f)‖²_HS`. -/
theorem sum_norm_inner_normalizedCoeff (f : EuclideanSpace ℂ G) :
    ∑ k, ‖⟪normalizedCoeff ρ k, f⟫_ℂ‖ ^ 2 =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ i, Module.finrank ℂ (V i) * hilbertSchmidtSq (groupFourier (ρ i) f) := by
  rw [Fintype.sum_sigma, Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [hilbertSchmidtSq_groupFourier_eq_sum (ρ i) (stdOrthonormalBasis ℂ (V i)), Fintype.sum_prod_type,
    Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun b => ?_
  simp only [normalizedCoeff, inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Real.sq_sqrt (by positivity)]
  ring

/-- **Bessel's inequality** for the Fourier transform: for pairwise inequivalent irreducible
unitary representations, `∑ᵢ dᵢ ‖ρ̂ᵢ(f)‖²_HS ≤ |G| ∑_g |f g|²`. -/
theorem sum_finrank_mul_hilbertSchmidtSq_le [∀ i, (ρ i).IsIrreducible]
    (hρ : ∀ i, IsUnitaryRepresentation (ρ i)) (hne : PairwiseInequivalent ρ) (f : G → ℂ) :
    ∑ i, Module.finrank ℂ (V i) * hilbertSchmidtSq (groupFourier (ρ i) f) ≤
      Fintype.card G * ∑ g, ‖f g‖ ^ 2 := by
  have h := (orthonormal_normalizedCoeff hρ hne).sum_inner_products_le
    (WithLp.toLp 2 f : EuclideanSpace ℂ G) (s := Finset.univ)
  rw [sum_norm_inner_normalizedCoeff, EuclideanSpace.norm_sq_eq] at h
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [inv_mul_le_iff₀ hG] at h
  exact h

/-- The **degree sum bound** `∑ᵢ dᵢ² ≤ |G|` for pairwise inequivalent irreducible unitary
representations. -/
theorem sum_finrank_sq_le [∀ i, (ρ i).IsIrreducible] (hρ : ∀ i, IsUnitaryRepresentation (ρ i))
    (hne : PairwiseInequivalent ρ) : ∑ i, Module.finrank ℂ (V i) ^ 2 ≤ Fintype.card G := by
  classical
  have h := sum_finrank_mul_hilbertSchmidtSq_le hρ hne (deltaOne : G → ℂ)
  have h1 : ∑ g : G, ‖(deltaOne g : ℂ)‖ ^ 2 = 1 := by
    rw [Fintype.sum_eq_single 1 fun g hg => by simp [deltaOne_apply, hg]]
    simp [deltaOne_apply]
  simp only [groupFourier_deltaOne, hilbertSchmidtSq_one, h1, mul_one] at h
  have h2 : ((∑ i, Module.finrank ℂ (V i) ^ 2 : ℕ) : ℝ) ≤ Fintype.card G := by
    push_cast
    simpa [sq] using h
  exact_mod_cast h2

end Bessel

section SingleBessel

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {ρ : Representation ℂ G V}

/-- For one irreducible unitary representation, `dim V ‖ρ̂(f)‖²_HS ≤ |G| ∑_g |f g|²`. -/
theorem finrank_mul_hilbertSchmidtSq_le [ρ.IsIrreducible] (hρ : IsUnitaryRepresentation ρ)
    (f : G → ℂ) :
    Module.finrank ℂ V * hilbertSchmidtSq (groupFourier ρ f) ≤ Fintype.card G * ∑ g, ‖f g‖ ^ 2 := by
  have h := sum_finrank_mul_hilbertSchmidtSq_le (ι := Unit) (V := fun _ => V) (ρ := fun _ => ρ)
    (fun _ => hρ) (fun i j hij => absurd (Subsingleton.elim i j) hij) f
  simpa using h

/-- An irreducible unitary representation has `(dim V)² ≤ |G|`. -/
theorem finrank_sq_le [ρ.IsIrreducible] (hρ : IsUnitaryRepresentation ρ) :
    Module.finrank ℂ V ^ 2 ≤ Fintype.card G := by
  have h := sum_finrank_sq_le (ι := Unit) (V := fun _ => V) (ρ := fun _ => ρ)
    (fun _ => hρ) (fun i j hij => absurd (Subsingleton.elim i j) hij)
  simpa using h

end SingleBessel

section Complete

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]

/-- A complete family of irreducible unitary representations: pairwise inequivalent, with
`∑ᵢ dᵢ² = |G|`. -/
structure IsCompleteFamily (ρ : ∀ i, Representation ℂ G (V i)) : Prop where
  isIrreducible : ∀ i, (ρ i).IsIrreducible
  isUnitary : ∀ i, IsUnitaryRepresentation (ρ i)
  pairwiseInequivalent : PairwiseInequivalent ρ
  sum_finrank_sq : ∑ i, Module.finrank ℂ (V i) ^ 2 = Fintype.card G

variable {ρ : ∀ i, Representation ℂ G (V i)}

/-- For a complete family the normalized matrix coefficients form an orthonormal basis of
`ℓ²(G)`. -/
theorem IsCompleteFamily.exists_orthonormalBasis (hρ : IsCompleteFamily ρ) :
    ∃ b : OrthonormalBasis ((i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i)))
      ℂ (EuclideanSpace ℂ G), ⇑b = normalizedCoeff ρ := by
  have := hρ.isIrreducible
  have hon := orthonormal_normalizedCoeff (G := G) hρ.isUnitary hρ.pairwiseInequivalent
  have hcard : Fintype.card ((i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i)))
      = Module.finrank ℂ (EuclideanSpace ℂ G) := by
    rw [finrank_euclideanSpace, ← hρ.sum_finrank_sq, Fintype.card_sigma]
    simp [sq]
  have : Nonempty ((i : ι) × Fin (Module.finrank ℂ (V i)) × Fin (Module.finrank ℂ (V i))) := by
    rw [← Fintype.card_pos_iff, hcard, finrank_euclideanSpace]
    exact Fintype.card_pos
  let B := basisOfOrthonormalOfCardEqFinrank hon hcard
  refine ⟨B.toOrthonormalBasis (by simpa [B] using hon), ?_⟩
  simp [B]

/-- **Plancherel formula**: `∑ᵢ dᵢ ‖ρ̂ᵢ(f)‖²_HS = |G| ∑_g |f g|²` for a complete family. -/
theorem IsCompleteFamily.sum_finrank_mul_hilbertSchmidtSq (hρ : IsCompleteFamily ρ) (f : G → ℂ) :
    ∑ i, Module.finrank ℂ (V i) * hilbertSchmidtSq (groupFourier (ρ i) f) =
      Fintype.card G * ∑ g, ‖f g‖ ^ 2 := by
  obtain ⟨b, hb⟩ := hρ.exists_orthonormalBasis
  have h := b.sum_sq_norm_inner_right (WithLp.toLp 2 f : EuclideanSpace ℂ G)
  rw [hb, sum_norm_inner_normalizedCoeff, EuclideanSpace.norm_sq_eq] at h
  have hG : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [inv_mul_eq_iff_eq_mul₀ hG.ne'] at h
  exact h

omit [Fintype G] in
/-- `∑_{a,b} ⟪σ x e_b, e_a⟫ ⟪e_a, A e_b⟫ = tr (σ x⁻¹ A)` for a unitary `σ`. -/
theorem sum_inner_rep_mul_inner {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] {σ : Representation ℂ G W} (hσ : IsUnitaryRepresentation σ)
    {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℂ W) (A : Module.End ℂ W) (x : G) :
    ∑ a, ∑ b, ⟪σ x (e b), e a⟫_ℂ * ⟪e a, A (e b)⟫_ℂ = LinearMap.trace ℂ W (σ x⁻¹ * A) := by
  rw [LinearMap.trace_eq_sum_inner _ e, Finset.sum_comm]
  refine Fintype.sum_congr _ _ fun b => ?_
  rw [e.sum_inner_mul_inner, Module.End.mul_apply, ← hσ.inner_inv_apply, inv_inv]

/-- **Fourier inversion**: `f x = |G|⁻¹ ∑ᵢ dᵢ tr (ρᵢ(x⁻¹) ρ̂ᵢ(f))` for a complete family. -/
theorem IsCompleteFamily.fourier_inversion (hρ : IsCompleteFamily ρ) (f : G → ℂ) (x : G) :
    f x = ∑ i, (Module.finrank ℂ (V i) / Fintype.card G : ℂ) *
      LinearMap.trace ℂ (V i) (ρ i x⁻¹ * groupFourier (ρ i) f) := by
  classical
  obtain ⟨b, hb⟩ := hρ.exists_orthonormalBasis
  have h := b.sum_inner_mul_inner (EuclideanSpace.single x 1) (WithLp.toLp 2 f)
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul, hb] at h
  rw [← h, Fintype.sum_sigma]
  refine Fintype.sum_congr _ _ fun i => ?_
  rw [← sum_inner_rep_mul_inner (hρ.isUnitary i) (stdOrthonormalBasis ℂ (V i)), Finset.mul_sum,
    Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_congr _ _ fun c => ?_
  simp only [normalizedCoeff, PiLp.smul_apply, matrixCoeff_apply, inner_smul_left,
    Complex.conj_ofReal, inner_matrixCoeff, smul_eq_mul]
  have hs : ((√(Module.finrank ℂ (V i) / Fintype.card G : ℝ) : ℝ) : ℂ) *
      ((√(Module.finrank ℂ (V i) / Fintype.card G : ℝ) : ℝ) : ℂ) =
      (Module.finrank ℂ (V i) / Fintype.card G : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    rfl
  rw [← hs]
  ring

/-- **Uniqueness**: a function whose Fourier transforms at a complete family vanish is zero. -/
theorem IsCompleteFamily.eq_zero_of_groupFourier (hρ : IsCompleteFamily ρ) {f : G → ℂ}
    (hf : ∀ i, groupFourier (ρ i) f = 0) : f = 0 := by
  funext x
  rw [hρ.fourier_inversion f x]
  simp [hf]

/-- The Fourier transform at a complete family is injective. -/
theorem IsCompleteFamily.groupFourier_injective (hρ : IsCompleteFamily ρ) {f f' : G → ℂ}
    (h : ∀ i, groupFourier (ρ i) f = groupFourier (ρ i) f') : f = f' := by
  have := hρ.eq_zero_of_groupFourier (f := f - f') fun i => by
    rw [groupFourier_sub, h i, sub_self]
  exact sub_eq_zero.mp this

/-- **Completeness**: every irreducible unitary representation is equivalent to a member of a
complete family. -/
theorem IsCompleteFamily.exists_equiv (hρ : IsCompleteFamily ρ) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ G W) [σ.IsIrreducible] (hσ : IsUnitaryRepresentation σ) :
    ∃ i, Nonempty (Representation.Equiv σ (ρ i)) := by
  by_contra hcon
  simp only [not_exists, not_nonempty_iff] at hcon
  have := hρ.isIrreducible
  obtain ⟨b, hb⟩ := hρ.exists_orthonormalBasis
  have := nontrivial_of_isIrreducible σ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  have hzero : matrixCoeff σ u u = 0 := by
    rw [← b.sum_repr' (matrixCoeff σ u u)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : IsEmpty (Representation.Equiv σ (ρ k.1)) := hcon k.1
    rw [hb]
    simp only [normalizedCoeff, inner_smul_left, inner_matrixCoeff_eq_zero hσ, mul_zero, zero_smul]
  have h1 := congrArg (fun y : EuclideanSpace ℂ G => y 1) hzero
  simp only [matrixCoeff_apply, map_one, Module.End.one_apply, PiLp.zero_apply,
    inner_self_eq_zero] at h1
  exact hu h1

end Complete

section Restrict

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V}

@[simp] theorem coe_toRepresentation_apply (W : Subrepresentation ρ) (g : G) (x : W.toSubmodule) :
    ((W.toRepresentation g x : W.toSubmodule) : V) = ρ g x := rfl

/-- A subrepresentation of `W.toRepresentation`, pushed to a subrepresentation of `ρ`. -/
def subrepPush (W : Subrepresentation ρ) (S : Subrepresentation W.toRepresentation) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map W.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨W.toRepresentation g x, S.apply_mem_toSubmodule g hx, rfl⟩

theorem finrank_subrepPush (W : Subrepresentation ρ) (S : Subrepresentation W.toRepresentation) :
    Module.finrank ℂ (subrepPush W S).toSubmodule = Module.finrank ℂ S.toSubmodule :=
  Submodule.finrank_map_subtype_eq _ _

theorem subrepPush_le (W : Subrepresentation ρ) (S : Subrepresentation W.toRepresentation) :
    subrepPush W S ≤ W := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

/-- A nonzero subrepresentation of a finite-dimensional representation contains an irreducible
subrepresentation. -/
theorem exists_isIrreducible_le [FiniteDimensional ℂ V] {K : Subrepresentation ρ} (hK : K ≠ ⊥) :
    ∃ W : Subrepresentation ρ, W ≤ K ∧ W ≠ ⊥ ∧ W.toRepresentation.IsIrreducible := by
  classical
  have hex : ∃ m, ∃ W : Subrepresentation ρ, W ≤ K ∧ W ≠ ⊥ ∧
      Module.finrank ℂ W.toSubmodule = m := ⟨_, K, le_rfl, hK, rfl⟩
  obtain ⟨W, hWK, hW, hWm⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Subrepresentation ρ, W' ≤ K → W' ≠ ⊥ →
      Module.finrank ℂ W.toSubmodule ≤ Module.finrank ℂ W'.toSubmodule := by
    intro W' hW'K hW'
    rw [hWm]
    exact Nat.find_min' hex ⟨W', hW'K, hW', rfl⟩
  refine ⟨W, hWK, hW, ?_⟩
  have hne : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.ext h)
  have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h' : (⊥ : Submodule ℂ W.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · by_cases hS : S = ⊥
    · exact Or.inl hS
    right
    have hS' : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.ext h)
    have h1 : 1 ≤ Module.finrank ℂ S.toSubmodule := Submodule.one_le_finrank_iff.mpr hS'
    have hpush : subrepPush W S ≠ ⊥ := by
      intro h
      have h0 : Module.finrank ℂ (subrepPush W S).toSubmodule = 0 := by
        rw [h]
        exact finrank_bot ℂ V
      rw [finrank_subrepPush] at h0
      omega
    have h2 := hmin (subrepPush W S) ((subrepPush_le W S).trans hWK) hpush
    rw [finrank_subrepPush] at h2
    exact Subrepresentation.ext
      (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h2))

/-- A one-dimensional representation is irreducible. -/
theorem isIrreducible_of_finrank_eq_one (h : Module.finrank ℂ V = 1) : ρ.IsIrreducible := by
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ h
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h'' : (⊥ : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule h'
    exact bot_ne_top h''
  · have hle := Submodule.finrank_le S.toSubmodule
    rw [h] at hle
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
    · left
      exact Subrepresentation.ext (Submodule.finrank_eq_zero.mp h0)
    · right
      exact Subrepresentation.ext (Submodule.eq_top_of_finrank_eq (h1.trans h.symm))

variable [Fintype G]

theorem coe_groupFourier_subrep (W : Subrepresentation ρ) (f : G → ℂ) (x : W.toSubmodule) :
    ((groupFourier W.toRepresentation f x : W.toSubmodule) : V) = groupFourier ρ f x := by
  simp [groupFourier_apply]

/-- Equivalences of representations intertwine Fourier transforms. -/
theorem equiv_groupFourier_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} (φ : Representation.Equiv ρ σ) (f : G → ℂ) (x : V) :
    φ (groupFourier ρ f x) = groupFourier σ f (φ x) := by
  have h : ∀ g, φ (ρ g x) = σ g (φ x) := fun g =>
    Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g x
  simp only [groupFourier_apply, map_sum, map_smul, h]

end Restrict

section UnitaryMaschke

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ρ : Representation ℂ G V}

/-- **Unitary Maschke**: the orthogonal complement of an invariant subspace of a unitary
representation is invariant. -/
theorem IsUnitaryRepresentation.apply_mem_orthogonal (hρ : IsUnitaryRepresentation ρ)
    {K : Submodule ℂ V} (hK : ∀ g, ∀ v ∈ K, ρ g v ∈ K) (g : G) {v : V} (hv : v ∈ Kᗮ) :
    ρ g v ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← hρ.inner_inv_apply]
  exact hv _ (hK g⁻¹ u hu)

/-- The orthogonal complement of a subrepresentation of a unitary representation. -/
def orthogonalSubrep (hρ : IsUnitaryRepresentation ρ) (W : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := W.toSubmoduleᗮ
  apply_mem_toSubmodule g _ hv :=
    hρ.apply_mem_orthogonal (fun g _ hv => W.apply_mem_toSubmodule g hv) g hv

/-- A subrepresentation of a unitary representation is unitary. -/
theorem IsUnitaryRepresentation.subrep (hρ : IsUnitaryRepresentation ρ) (W : Subrepresentation ρ) :
    IsUnitaryRepresentation W.toRepresentation := fun g x y => hρ g x y

end UnitaryMaschke

section FourierKernel

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] {U : ι → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]

/-- `f ↦ (τ̂ᵢ(f))ᵢ` as a linear map on `ℓ²(G)`. -/
def fourierMap (τ : ∀ i, Representation ℂ G (U i)) :
    EuclideanSpace ℂ G →ₗ[ℂ] ∀ i, Module.End ℂ (U i) where
  toFun f i := groupFourier (τ i) f
  map_add' f f' := by funext i; exact groupFourier_add (τ i) f f'
  map_smul' c f := by funext i; exact groupFourier_smul (τ i) c f

/-- The common kernel of the Fourier transforms `τ̂ᵢ`, a subrepresentation of `ℓ²(G)`. -/
def fourierKernel (τ : ∀ i, Representation ℂ G (U i)) : Subrepresentation (leftRegular G) where
  toSubmodule := LinearMap.ker (fourierMap τ)
  apply_mem_toSubmodule g f hf := by
    rw [LinearMap.mem_ker] at hf ⊢
    funext i
    have hi : groupFourier (τ i) f = 0 := congrFun hf i
    change groupFourier (τ i) (fun h => f (g⁻¹ * h)) = 0
    rw [groupFourier_comp_mul_left, hi, mul_zero]

omit [Fintype ι] in
theorem mem_fourierKernel {τ : ∀ i, Representation ℂ G (U i)} {f : EuclideanSpace ℂ G} :
    f ∈ (fourierKernel τ).toSubmodule ↔ ∀ i, groupFourier (τ i) f = 0 := by
  change fourierMap τ f = 0 ↔ _
  exact funext_iff

/-- If `∑ᵢ dᵢ² < |G|` the common kernel of the `τ̂ᵢ` is nonzero. -/
theorem fourierKernel_ne_bot [∀ i, FiniteDimensional ℂ (U i)] (τ : ∀ i, Representation ℂ G (U i))
    (h : ∑ i, Module.finrank ℂ (U i) ^ 2 < Fintype.card G) : fourierKernel τ ≠ ⊥ := by
  intro hbot
  have hker : LinearMap.ker (fourierMap τ) = ⊥ := congrArg Subrepresentation.toSubmodule hbot
  have h1 := LinearMap.finrank_range_add_finrank_ker (fourierMap τ)
  rw [hker, finrank_bot, add_zero, finrank_euclideanSpace] at h1
  have h2 := Submodule.finrank_le (LinearMap.range (fourierMap τ))
  rw [Module.finrank_pi_fintype, h1] at h2
  simp only [Module.finrank_linearMap] at h2
  have h3 : ∑ i, Module.finrank ℂ (U i) * Module.finrank ℂ (U i) =
      ∑ i, Module.finrank ℂ (U i) ^ 2 := by simp [sq]
  omega

end FourierKernel

section Existence

variable {G : Type*} [Group G] [Fintype G]

/-- In a subrepresentation `W` of `ℓ²(G)`, a vector `y ∈ W` whose Fourier transform vanishes on
`W` is zero (apply `ρ̂(y)` to `δ₁ = w₀ + w₁` with `w₀ ∈ W`, `w₁ ∈ W⊥`). -/
theorem eq_zero_of_groupFourier_subrep_eq_zero (W : Subrepresentation (leftRegular G))
    {y : EuclideanSpace ℂ G} (hy : y ∈ W.toSubmodule)
    (h : ∀ w ∈ W.toSubmodule, groupFourier (leftRegular G) y w = 0) : y = 0 := by
  classical
  obtain ⟨w₀, hw₀, w₁, hw₁, hsum⟩ :=
    W.toSubmodule.exists_add_mem_mem_orthogonal (EuclideanSpace.single (1 : G) (1 : ℂ))
  have hδ : groupFourier (leftRegular G) y (EuclideanSpace.single 1 1) = y := by
    ext g
    rw [groupFourier_leftRegular_single]
    simp
  have hperp : groupFourier (leftRegular G) y w₁ ∈ W.toSubmoduleᗮ := by
    rw [groupFourier_apply]
    refine Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_
    exact isUnitaryRepresentation_leftRegular.apply_mem_orthogonal
      (fun g _ hv => W.apply_mem_toSubmodule g hv) g hw₁
  rw [hsum, map_add, h w₀ hw₀, zero_add] at hδ
  rw [hδ] at hperp
  exact inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal hy hperp)

variable {ι : Type*} [Fintype ι] {U : ι → Type*} [∀ i, AddCommGroup (U i)] [∀ i, Module ℂ (U i)]
  [∀ i, FiniteDimensional ℂ (U i)]

/-- **Extension**: if `∑ᵢ dᵢ² < |G|`, then `ℓ²(G)` contains an irreducible subrepresentation
inequivalent to every `τᵢ`. -/
theorem exists_subrep_isEmpty_equiv (τ : ∀ i, Representation ℂ G (U i))
    (h : ∑ i, Module.finrank ℂ (U i) ^ 2 < Fintype.card G) :
    ∃ W : Subrepresentation (leftRegular G), W.toRepresentation.IsIrreducible ∧
      ∀ i, IsEmpty (Representation.Equiv W.toRepresentation (τ i)) := by
  obtain ⟨W, hWK, hW, hirr⟩ := exists_isIrreducible_le (fourierKernel_ne_bot τ h)
  refine ⟨W, hirr, fun i => ⟨fun φ => ?_⟩⟩
  have hnt : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.ext h)
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hnt
  refine hy0 (eq_zero_of_groupFourier_subrep_eq_zero W hy fun w hw => ?_)
  have hyK : groupFourier (τ i) y = 0 := mem_fourierKernel.mp (hWK hy) i
  have h1 : φ (groupFourier W.toRepresentation y ⟨w, hw⟩) = 0 := by
    rw [equiv_groupFourier_apply, hyK, LinearMap.zero_apply]
  have h2 : groupFourier W.toRepresentation y ⟨w, hw⟩ = 0 := by simpa using h1
  simpa [h2] using (coe_groupFourier_subrep W y ⟨w, hw⟩).symm

/-- **Existence of a complete family**: `ℓ²(G)` contains a complete family of irreducible
subrepresentations. -/
theorem exists_isCompleteFamily_subrep :
    ∃ (n : ℕ) (W : Fin n → Subrepresentation (leftRegular G)),
      IsCompleteFamily (V := fun i => (W i).toSubmodule) (fun i => (W i).toRepresentation) := by
  have hu : ∀ W : Subrepresentation (leftRegular G),
      IsUnitaryRepresentation (V := W.toSubmodule) W.toRepresentation :=
    fun W => (isUnitaryRepresentation_leftRegular (G := G)).subrep W
  have key : ∀ (m n : ℕ) (W : Fin n → Subrepresentation (leftRegular G)),
      (∀ i, (W i).toRepresentation.IsIrreducible) →
      PairwiseInequivalent (V := fun i => (W i).toSubmodule) (fun i => (W i).toRepresentation) →
      Fintype.card G - ∑ i, Module.finrank ℂ (W i).toSubmodule ^ 2 ≤ m →
      ∃ (n : ℕ) (W : Fin n → Subrepresentation (leftRegular G)),
        IsCompleteFamily (V := fun i => (W i).toSubmodule) (fun i => (W i).toRepresentation) := by
    intro m
    induction m with
    | zero =>
      intro n W hirr hne hm
      have hle := sum_finrank_sq_le (V := fun i => (W i).toSubmodule) (ρ := fun i => (W i).toRepresentation)
        (fun i => hu (W i)) hne
      exact ⟨n, W, ⟨hirr, fun i => hu (W i), hne, by omega⟩⟩
    | succ m ih =>
      intro n W hirr hne hm
      have hle := sum_finrank_sq_le (V := fun i => (W i).toSubmodule) (ρ := fun i => (W i).toRepresentation)
        (fun i => hu (W i)) hne
      by_cases heq : ∑ i, Module.finrank ℂ (W i).toSubmodule ^ 2 = Fintype.card G
      · exact ⟨n, W, ⟨hirr, fun i => hu (W i), hne, heq⟩⟩
      obtain ⟨W', hirr', hne'⟩ :=
        exists_subrep_isEmpty_equiv (fun i => (W i).toRepresentation) (lt_of_le_of_ne hle heq)
      refine ih (n + 1) (Fin.cons W' W) ?_ ?_ ?_
      · intro i
        induction i using Fin.cases with
        | zero => exact hirr'
        | succ j => exact hirr j
      · intro i j hij
        induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact absurd rfl hij
          | succ j => exact hne' j
        | succ i =>
          induction j using Fin.cases with
          | zero => exact ⟨fun φ => (hne' i).false φ.symm⟩
          | succ j => exact hne i j fun h => hij (by rw [h])
      · have hd : 0 < Module.finrank ℂ W'.toSubmodule := by
          have := nontrivial_of_isIrreducible W'.toRepresentation
          exact Module.finrank_pos
        have hs : ∑ i, Module.finrank ℂ ((Fin.cons W' W : Fin (n + 1) → _) i).toSubmodule ^ 2 =
            Module.finrank ℂ W'.toSubmodule ^ 2 + ∑ i, Module.finrank ℂ (W i).toSubmodule ^ 2 :=
          Fin.sum_univ_succ _
        rw [hs]
        have : 1 ≤ Module.finrank ℂ W'.toSubmodule ^ 2 := Nat.one_le_pow _ _ hd
        omega
  exact key (Fintype.card G) 0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) (by simp)

/-- Every irreducible unitary representation of a finite group occurs in `ℓ²(G)`. -/
theorem exists_subrep_equiv {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ G W) [σ.IsIrreducible]
    (hσ : IsUnitaryRepresentation σ) :
    ∃ U : Subrepresentation (leftRegular G), U.toRepresentation.IsIrreducible ∧
      Nonempty (Representation.Equiv σ U.toRepresentation) := by
  obtain ⟨n, W, hW⟩ := exists_isCompleteFamily_subrep (G := G)
  obtain ⟨i, hi⟩ := hW.exists_equiv σ hσ
  exact ⟨W i, hW.isIrreducible i, hi⟩


end Existence

section UpperBound

variable {G : Type*} [Group G] [Fintype G]

section Single

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {ρ : Representation ℂ G V}

omit [FiniteDimensional ℂ V] in
/-- `ρ̂(p - u) = ρ̂(p) - P`, where `P` is the group average. -/
theorem groupFourier_sub_uniform (ρ : Representation ℂ G V) (p : G → ℝ) :
    groupFourier ρ (fun g => ((p g - uniform G g : ℝ) : ℂ)) =
      groupFourier ρ (fun g => (p g : ℂ)) - groupAverage ρ := by
  have h : (fun g => ((p g - uniform G g : ℝ) : ℂ)) =
      (fun g => (p g : ℂ)) - fun g => ((uniform G g : ℝ) : ℂ) := by
    funext g
    simp
  rw [h, groupFourier_sub, groupFourier_uniform]

/-- `‖ρ̂(p) - P‖²_HS = ‖ρ̂(p)‖²_HS - dim V^G` for a law `p` and a unitary `ρ`. -/
theorem hilbertSchmidtSq_groupFourier_sub_groupAverage (hρ : IsUnitaryRepresentation ρ)
    {p : G → ℝ} (hp : ∑ g, p g = 1) :
    hilbertSchmidtSq (groupFourier ρ (fun g => (p g : ℂ)) - groupAverage ρ) =
      hilbertSchmidtSq (groupFourier ρ (fun g => (p g : ℂ))) - Module.finrank ℂ ρ.invariants := by
  have hp' : ∑ g, (p g : ℂ) = 1 := by exact_mod_cast hp
  have hHS := hilbertSchmidtSq_groupAverage hρ
  set F := groupFourier ρ (fun g => (p g : ℂ))
  set A := groupAverage ρ
  have hFA : F * A = A := groupFourier_mul_groupAverage ρ hp'
  have hAF : A * F = A := groupAverage_mul_groupFourier ρ hp'
  have hAA : A * A = A := groupAverage_mul_groupAverage ρ
  have hAd : LinearMap.adjoint A = A := adjoint_groupAverage hρ
  have hFdA : LinearMap.adjoint F * A = A := by
    have h := congrArg LinearMap.adjoint hAF
    rw [Module.End.mul_eq_comp, LinearMap.adjoint_comp, hAd] at h
    exact h
  have hexp : LinearMap.adjoint (F - A) * (F - A) = LinearMap.adjoint F * F - A := by
    rw [map_sub, hAd, sub_mul, mul_sub, mul_sub, hFdA, hAF, hAA]
    abel
  have hA : (LinearMap.trace ℂ V A).re = Module.finrank ℂ ρ.invariants := by
    rw [← hHS, hilbertSchmidtSq, hAd, hAA]
  rw [hilbertSchmidtSq, hexp, map_sub, Complex.sub_re, hA]
  rfl

/-- `‖ρ̂(p)^t‖²_HS ≤ dim V · ‖ρ̂(p)‖^{2t}`. -/
theorem hilbertSchmidtSq_pow_le (A : Module.End ℂ V) (t : ℕ) :
    hilbertSchmidtSq (A ^ t) ≤
      Module.finrank ℂ V * ‖LinearMap.toContinuousLinearMap A‖ ^ (2 * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_add, mul_one, pow_add, mul_comm (‖_‖ ^ (2 * t)), ← mul_assoc]
    calc hilbertSchmidtSq (A * A ^ t)
        ≤ ‖LinearMap.toContinuousLinearMap A‖ ^ 2 * hilbertSchmidtSq (A ^ t) :=
          hilbertSchmidtSq_mul_le_left _ _
      _ ≤ ‖LinearMap.toContinuousLinearMap A‖ ^ 2 *
            (Module.finrank ℂ V * ‖LinearMap.toContinuousLinearMap A‖ ^ (2 * t)) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = _ := by ring

omit [FiniteDimensional ℂ V] in
/-- On a trivial representation (every vector invariant) `ρ̂(p) = P` for a law `p`. -/
theorem groupFourier_eq_groupAverage_of_forall_mem_invariants (ρ : Representation ℂ G V)
    (h : ∀ v, v ∈ ρ.invariants) {p : G → ℝ} (hp : ∑ g, p g = 1) :
    groupFourier ρ (fun g => (p g : ℂ)) = groupAverage ρ := by
  have hp' : ∑ g, (p g : ℂ) = 1 := by exact_mod_cast hp
  ext v
  have hv : ∀ g, ρ g v = v := fun g => (Representation.mem_invariants ρ v).mp (h v) g
  rw [groupFourier_apply, groupAverage_apply_of_mem_invariants ρ (h v)]
  simp only [hv, ← Finset.sum_smul, hp', one_smul]

end Single

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ G (V i)}

/-- Plancherel for `p - u`: `|G| ∑_g (p g - u g)² = ∑ᵢ dᵢ ‖ρ̂ᵢ(p) - Pᵢ‖²_HS`. -/
theorem IsCompleteFamily.card_mul_sum_sub_uniform_sq (hρ : IsCompleteFamily ρ) (p : G → ℝ) :
    Fintype.card G * ∑ g, (p g - uniform G g) ^ 2 =
      ∑ i, Module.finrank ℂ (V i) *
        hilbertSchmidtSq (groupFourier (ρ i) (fun g => (p g : ℂ)) - groupAverage (ρ i)) := by
  have h := hρ.sum_finrank_mul_hilbertSchmidtSq (fun g => ((p g - uniform G g : ℝ) : ℂ))
  simp only [groupFourier_sub_uniform, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  exact h.symm

/-- **Upper bound lemma** (Diaconis–Shahshahani): for a law `p` on `G`,
`4 ‖p - u‖²_TV ≤ ∑ᵢ dᵢ ‖ρ̂ᵢ(p) - Pᵢ‖²_HS`. -/
theorem IsCompleteFamily.four_mul_tvDist_sq_le (hρ : IsCompleteFamily ρ) (p : G → ℝ) :
    4 * tvDist p (uniform G) ^ 2 ≤
      ∑ i, Module.finrank ℂ (V i) *
        hilbertSchmidtSq (groupFourier (ρ i) (fun g => (p g : ℂ)) - groupAverage (ρ i)) := by
  rw [← hρ.card_mul_sum_sub_uniform_sq]
  have h := tvDist_le_sqrt_card_mul p (uniform G)
  have h0 : 0 ≤ tvDist p (uniform G) := by
    rw [tvDist]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hs : 0 ≤ ∑ g, (p g - uniform G g) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc : (0 : ℝ) ≤ Fintype.card G := Nat.cast_nonneg _
  have h2 : (2 * tvDist p (uniform G)) ^ 2 ≤ (√(Fintype.card G) * √(∑ g, (p g - uniform G g) ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hs] at h2
  linarith [h2]

/-- **Upper bound lemma** over the nontrivial blocks: if every `ρᵢ` with `i ∉ s` is trivial
(fixes every vector), then `4 ‖p - u‖²_TV ≤ ∑_{i ∈ s} dᵢ ‖ρ̂ᵢ(p)‖²_HS` for a law `p`. -/
theorem IsCompleteFamily.four_mul_tvDist_sq_le_sum (hρ : IsCompleteFamily ρ) {p : G → ℝ}
    (hp : ∑ g, p g = 1) (s : Finset ι) (hs : ∀ i ∉ s, ∀ v, v ∈ (ρ i).invariants) :
    4 * tvDist p (uniform G) ^ 2 ≤
      ∑ i ∈ s, Module.finrank ℂ (V i) * hilbertSchmidtSq (groupFourier (ρ i) (fun g => (p g : ℂ))) := by
  refine (hρ.four_mul_tvDist_sq_le p).trans ?_
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by
    rw [groupFourier_eq_groupAverage_of_forall_mem_invariants (ρ i) (hs i hi) hp, sub_self,
      (hilbertSchmidtSq_eq_zero_iff _).mpr rfl, mul_zero]]
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [hilbertSchmidtSq_groupFourier_sub_groupAverage (hρ.isUnitary i) hp]
  linarith [(Nat.cast_nonneg (Module.finrank ℂ (ρ i).invariants) : (0 : ℝ) ≤ _)]

/-- **Upper bound lemma** for random walks: for a law `p` and `t` steps,
`4 ‖p^{*t} - u‖²_TV ≤ ∑_{i ∈ s} dᵢ² ‖ρ̂ᵢ(p)‖^{2t}`, with `s` as in
`four_mul_tvDist_sq_le_sum`. -/
theorem IsCompleteFamily.four_mul_tvDist_groupConvPow_sq_le (hρ : IsCompleteFamily ρ)
    {p : G → ℝ} (hp : ∑ g, p g = 1) (s : Finset ι) (hs : ∀ i ∉ s, ∀ v, v ∈ (ρ i).invariants)
    (t : ℕ) :
    4 * tvDist (groupConvPow p t) (uniform G) ^ 2 ≤
      ∑ i ∈ s, (Module.finrank ℂ (V i) : ℝ) ^ 2 *
        ‖LinearMap.toContinuousLinearMap (groupFourier (ρ i) (fun g => (p g : ℂ)))‖ ^ (2 * t) := by
  have hpt : ∑ g, groupConvPow p t g = 1 := by rw [sum_groupConvPow, hp, one_pow]
  refine (hρ.four_mul_tvDist_sq_le_sum hpt s hs).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [groupFourier_ofReal_groupConvPow, sq, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hilbertSchmidtSq_pow_le _ t) (Nat.cast_nonneg _)

end UpperBound

section ClassFunction

variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A class function on `G`: constant on conjugacy classes. -/
def IsClassFunction {k : Type*} (f : G → k) : Prop := ∀ g h, f (h * g * h⁻¹) = f g

theorem groupFourier_commute (ρ : Representation ℂ G V) {f : G → ℂ} (hf : IsClassFunction f)
    (h : G) : groupFourier ρ f * ρ h = ρ h * groupFourier ρ f := by
  simp only [groupFourier, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← map_mul]
  refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
  have h1 : f (h⁻¹ * g * h⁻¹⁻¹) = f g := hf g h⁻¹
  rw [inv_inv] at h1
  have h2 : h * (h⁻¹ * g * h) = g * h := by group
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv, h1, h2]

variable [FiniteDimensional ℂ V]

/-- The Fourier transform of a class function at an irreducible `ρ` is the scalar
`(∑_g f g χ_ρ(g)) / dim V`. -/
theorem groupFourier_eq_smul_one (ρ : Representation ℂ G V) [ρ.IsIrreducible] {f : G → ℂ}
    (hf : IsClassFunction f) :
    groupFourier ρ f = ((∑ g, f g * ρ.character g) / Module.finrank ℂ V) • 1 := by
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_commute ρ (groupFourier ρ f)
    fun g => groupFourier_commute ρ hf g
  have := nontrivial_of_isIrreducible ρ
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have htr : LinearMap.trace ℂ V (groupFourier ρ f) = ∑ g, f g * ρ.character g := by
    simp [groupFourier, map_sum, Representation.character]
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at htr
  rw [hc, ← htr, mul_div_cancel_right₀ _ hd]

end ClassFunction

section ClassUpperBound

variable {G : Type*} [Group G] [Fintype G]
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
variable {ρ : ∀ i, Representation ℂ G (V i)}

/-- **Upper bound lemma** for a conjugation-invariant step law, in character ratios:
`4 ‖p^{*t} - u‖²_TV ≤ ∑_{i ∈ s} dᵢ² |(∑_g p g χᵢ(g)) / dᵢ|^{2t}`, with `s` as in
`four_mul_tvDist_sq_le_sum`. -/
theorem IsCompleteFamily.four_mul_tvDist_groupConvPow_sq_le_char (hρ : IsCompleteFamily ρ)
    {p : G → ℝ} (hp : ∑ g, p g = 1) (hpc : IsClassFunction p) (s : Finset ι)
    (hs : ∀ i ∉ s, ∀ v, v ∈ (ρ i).invariants) (t : ℕ) :
    4 * tvDist (groupConvPow p t) (uniform G) ^ 2 ≤
      ∑ i ∈ s, (Module.finrank ℂ (V i) : ℝ) ^ 2 *
        ‖(∑ g, (p g : ℂ) * (ρ i).character g) / Module.finrank ℂ (V i)‖ ^ (2 * t) := by
  have hpt : ∑ g, groupConvPow p t g = 1 := by rw [sum_groupConvPow, hp, one_pow]
  refine (hρ.four_mul_tvDist_sq_le_sum hpt s hs).trans_eq (Finset.sum_congr rfl fun i _ => ?_)
  have := hρ.isIrreducible i
  have hpc' : IsClassFunction fun g => (p g : ℂ) := fun g h =>
    congrArg (fun x : ℝ => (x : ℂ)) (hpc g h)
  rw [groupFourier_ofReal_groupConvPow, groupFourier_eq_smul_one (ρ i) hpc', smul_pow, one_pow,
    hilbertSchmidtSq_smul, hilbertSchmidtSq_one, norm_pow]
  ring

end ClassUpperBound

end

end TheoremOS.RepresentationTheory
