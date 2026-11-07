import Mathlib

/-!
# Tensor products of finitely many matrices in the product basis

For a family `a : ι → Matrix m n R` indexed by a finite type, `piTensor a` is the matrix on
`ι → m` by `ι → n` with entries `∏ i, a i (x i) (y i)`: the tensor product `a₁ ⊗ ⋯ ⊗ a_N` written
in the computational (product) basis. Contents: multiplicativity, the identity, trace, transpose
and conjugate transpose, action on product vectors, scalars, splitting a sum index into a Kronecker
product, peeling off the first factor of a `Fin (N + 1)` index, unitary / Hermitian / positive
semidefinite factors, single-site operators `siteOp q u` (`u` on site `q`, identity elsewhere)
and their algebra, and permutation matrices of basis bijections.

Sources: M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
University Press, 2000, Section 2.1.7 (tensor products, `(A ⊗ B)(C ⊗ D) = AC ⊗ BD`); R. A. Horn
and C. R. Johnson, *Topics in Matrix Analysis*, Cambridge University Press, 1991, Section 4.2
(Kronecker product: mixed-product property, trace, adjoint, positivity). Textbook material; nothing
here is specific to a benchmark problem.

Bridges: a statement defining `tensorMatrix a := fun x y => ∏ i, a i (x i) (y i)` (or `tensor`,
`tensorKraus` with the same body) is `piTensor a` by `rfl`; the gate
`tensorMatrix fun i => if i = q then u else 1` is `siteOp q u` by `rfl`; a matrix
`fun x y => if x = σ y then 1 else 0` for a bijection `σ` of basis words is `permOp σ` by `rfl`.
Mathlib's Kronecker product `A ⊗ₖ B` appears through `piTensor_sum` and `piTensor_fin_succ`.
-/

namespace TheoremOS.LinearAlgebra

open Finset Matrix
open scoped BigOperators Kronecker

noncomputable section

variable {ι κ m n p R : Type*}

section CommSemiring

variable [Fintype ι] [CommSemiring R]

/-- The tensor product `⨂ i, a i` in the product basis. -/
def piTensor (a : ι → Matrix m n R) : Matrix (ι → m) (ι → n) R :=
  fun x y => ∏ i, a i (x i) (y i)

@[simp] lemma piTensor_apply (a : ι → Matrix m n R) (x : ι → m) (y : ι → n) :
    piTensor a x y = ∏ i, a i (x i) (y i) := rfl

lemma piTensor_transpose (a : ι → Matrix m n R) :
    (piTensor a)ᵀ = piTensor fun i => (a i)ᵀ := rfl

lemma piTensor_smul (c : ι → R) (a : ι → Matrix m n R) :
    piTensor (fun i => c i • a i) = (∏ i, c i) • piTensor a := by
  ext x y
  simp [Finset.prod_mul_distrib]

lemma piTensor_eq_zero_of_eq_zero {a : ι → Matrix m n R} {i : ι} (h : a i = 0) :
    piTensor a = 0 := by
  ext x y
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h])

/-- The mixed-product property `(⨂ a) (⨂ b) = ⨂ (a b)`. -/
theorem piTensor_mul [DecidableEq ι] [Fintype n] (a : ι → Matrix m n R) (b : ι → Matrix n p R) :
    piTensor a * piTensor b = piTensor fun i => a i * b i := by
  ext x z
  simp only [mul_apply, piTensor_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

theorem piTensor_one [DecidableEq ι] [DecidableEq m] :
    piTensor (fun _ : ι => (1 : Matrix m m R)) = 1 := by
  ext x y
  simp only [piTensor_apply, one_apply]
  rw [Fintype.prod_boole]
  by_cases h : x = y
  · simp [h]
  · rw [ite_eq_right (fun hxy => h (funext hxy)), ite_eq_right h]

theorem trace_piTensor [DecidableEq ι] [Fintype m] (a : ι → Matrix m m R) :
    (piTensor a).trace = ∏ i, (a i).trace := by
  simp only [Matrix.trace, Matrix.diag, piTensor_apply]
  rw [Fintype.prod_sum]

/-- `⨂ a` sends the product vector `x ↦ ∏ i, v i (x i)` to the product of the `a i *ᵥ v i`. -/
theorem piTensor_mulVec [DecidableEq ι] [Fintype n] (a : ι → Matrix m n R) (v : ι → n → R) :
    piTensor a *ᵥ (fun y => ∏ i, v i (y i)) = fun x => ∏ i, (a i *ᵥ v i) (x i) := by
  ext x
  simp only [mulVec, dotProduct, piTensor_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

/-- Inner products of product vectors factor. -/
theorem dotProduct_prod [DecidableEq ι] [Fintype n] (v w : ι → n → R) :
    (fun x : ι → n => ∏ i, v i (x i)) ⬝ᵥ (fun x => ∏ i, w i (x i)) = ∏ i, v i ⬝ᵥ w i := by
  simp only [dotProduct]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

/-- Splitting the index `ι ⊕ κ` gives Mathlib's Kronecker product, up to the basis relabeling
`(ι ⊕ κ → m) ≃ (ι → m) × (κ → m)`. -/
theorem piTensor_sum [Fintype κ] (a : ι ⊕ κ → Matrix m n R) :
    piTensor a = (piTensor (fun i => a (Sum.inl i)) ⊗ₖ piTensor (fun k => a (Sum.inr k))).submatrix
      (Equiv.sumArrowEquivProdArrow ι κ m) (Equiv.sumArrowEquivProdArrow ι κ n) := by
  ext x y
  simp [kroneckerMap_apply, Fintype.prod_sum_type]

/-- Peeling off the first factor of a `Fin (N + 1)` index. -/
theorem piTensor_fin_succ {N : ℕ} (a : Fin (N + 1) → Matrix m n R) (x : Fin (N + 1) → m)
    (y : Fin (N + 1) → n) :
    piTensor a x y = a 0 (x 0) (y 0) * piTensor (fun i : Fin N => a i.succ) (fun i => x i.succ)
      (fun i => y i.succ) := by
  simp [Fin.prod_univ_succ]

/-- Relabeling the factors relabels the basis words. -/
theorem piTensor_comp_equiv [Fintype κ] (e : κ ≃ ι) (a : ι → Matrix m n R) :
    piTensor (a ∘ e) = (piTensor a).submatrix (fun x => x ∘ e.symm) (fun y => y ∘ e.symm) := by
  ext x y
  simp only [piTensor_apply, submatrix_apply, Function.comp_apply]
  exact (Fintype.prod_equiv e _ _ (fun k => by simp)).trans rfl

end CommSemiring

section Star

variable [Fintype ι] [CommSemiring R] [StarRing R]

theorem piTensor_conjTranspose (a : ι → Matrix m n R) :
    (piTensor a)ᴴ = piTensor fun i => (a i)ᴴ := by
  ext x y
  simp [conjTranspose_apply, star_prod]

theorem isHermitian_piTensor {a : ι → Matrix m m R} (ha : ∀ i, (a i).IsHermitian) :
    (piTensor a).IsHermitian := by
  rw [IsHermitian, piTensor_conjTranspose]
  exact congrArg piTensor (funext ha)

end Star

section Unitary

variable [Fintype ι] [CommRing R] [StarRing R]

theorem piTensor_mem_unitaryGroup [DecidableEq ι] [Fintype m] [DecidableEq m]
    {a : ι → Matrix m m R} (ha : ∀ i, a i ∈ unitaryGroup m R) :
    piTensor a ∈ unitaryGroup (ι → m) R := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, piTensor_conjTranspose, piTensor_mul,
    ← piTensor_one]
  congr 1
  funext i
  simpa [star_eq_conjTranspose] using mem_unitaryGroup_iff.1 (ha i)

end Unitary

section RCLike

variable [Fintype ι] {𝕜 : Type*} [RCLike 𝕜]

open scoped MatrixOrder ComplexOrder in
theorem posSemidef_piTensor [DecidableEq ι] [Fintype m] [DecidableEq m] {a : ι → Matrix m m 𝕜}
    (ha : ∀ i, (a i).PosSemidef) : (piTensor a).PosSemidef := by
  choose b hb using fun i => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (ha i).nonneg
  have : piTensor a = (piTensor b)ᴴ * piTensor b := by
    rw [piTensor_conjTranspose, piTensor_mul]
    exact congrArg piTensor (funext fun i => by simpa [star_eq_conjTranspose] using hb i)
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

end RCLike

section SiteOp

variable [Fintype ι] [DecidableEq ι] [DecidableEq m] [CommSemiring R]

/-- The operator `u` on site `q` and the identity on every other site. -/
def siteOp (q : ι) (u : Matrix m m R) : Matrix (ι → m) (ι → m) R :=
  piTensor fun i => if i = q then u else 1

lemma siteOp_apply (q : ι) (u : Matrix m m R) (x y : ι → m) :
    siteOp q u x y = u (x q) (y q) * if ∀ i, i ≠ q → x i = y i then 1 else 0 := by
  rw [siteOp, piTensor_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  simp only [↓reduceIte]
  congr 1
  rw [Finset.prod_congr rfl fun i hi => by rw [ite_eq_right (Finset.ne_of_mem_erase hi), one_apply],
    Finset.prod_boole]
  simp

@[simp] lemma siteOp_one (q : ι) : siteOp q (1 : Matrix m m R) = 1 := by
  simp [siteOp, piTensor_one]

theorem siteOp_mul_siteOp [Fintype m] (q : ι) (u v : Matrix m m R) :
    siteOp q u * siteOp q v = siteOp q (u * v) := by
  rw [siteOp, siteOp, piTensor_mul, siteOp]
  congr 1
  funext i
  split_ifs <;> simp

/-- Operators on different sites commute. -/
theorem siteOp_commute [Fintype m] {q r : ι} (hqr : q ≠ r) (u v : Matrix m m R) :
    siteOp q u * siteOp r v = siteOp r v * siteOp q u := by
  rw [siteOp, siteOp, piTensor_mul, piTensor_mul]
  congr 1
  funext i
  by_cases hq : i = q
  · subst hq
    simp [hqr]
  · by_cases hr : i = r
    · subst hr
      simp [hq]
    · simp [hq, hr]

theorem siteOp_conjTranspose [StarRing R] (q : ι) (u : Matrix m m R) :
    (siteOp q u)ᴴ = siteOp q uᴴ := by
  rw [siteOp, piTensor_conjTranspose, siteOp]
  congr 1
  funext i
  split_ifs <;> simp

end SiteOp

section SiteOpUnitary

variable [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] [CommRing R] [StarRing R]

theorem siteOp_mem_unitaryGroup (q : ι) {u : Matrix m m R}
    (hu : u ∈ unitaryGroup m R) : siteOp q u ∈ unitaryGroup (ι → m) R :=
  piTensor_mem_unitaryGroup fun i => by
    split_ifs
    · exact hu
    · exact one_mem _

end SiteOpUnitary

section PermOp

variable [DecidableEq m] [CommSemiring R]

/-- The matrix of a bijection of basis words: column `y` is the basis vector `σ y`. -/
def permOp (σ : Equiv.Perm m) : Matrix m m R := fun x y => if x = σ y then 1 else 0

@[simp] lemma permOp_apply (σ : Equiv.Perm m) (x y : m) :
    (permOp σ : Matrix m m R) x y = if x = σ y then 1 else 0 := rfl

@[simp] lemma permOp_one : (permOp 1 : Matrix m m R) = 1 := by
  ext x y
  by_cases h : x = y <;> simp [one_apply, h]

/-- For an involution `f` of basis words, `fun x y => if x = f y then 1 else 0` is `permOp`. -/
lemma permOp_toPerm {f : m → m} (hf : Function.Involutive f) :
    (permOp (hf.toPerm f) : Matrix m m R) = fun x y => if x = f y then 1 else 0 := rfl

variable [Fintype m]

theorem permOp_mul (σ τ : Equiv.Perm m) :
    (permOp σ * permOp τ : Matrix m m R) = permOp (σ * τ) := by
  ext x z
  simp only [mul_apply, permOp_apply, ite_mul, one_mul, zero_mul, Equiv.Perm.mul_apply]
  rw [Finset.sum_eq_single (τ z)]
  · by_cases h : x = σ (τ z) <;> simp [h]
  · intro y _ hy
    simp [hy]
  · simp

theorem mulVec_permOp (σ : Equiv.Perm m) (v : m → R) :
    (permOp σ : Matrix m m R) *ᵥ v = fun x => v (σ.symm x) := by
  ext x
  simp only [mulVec, dotProduct, permOp_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single (σ.symm x)]
  · simp
  · intro y _ hy
    rw [ite_eq_right]
    rintro rfl
    exact hy (by simp)
  · simp

omit [Fintype m] in
theorem permOp_conjTranspose [StarRing R] (σ : Equiv.Perm m) :
    (permOp σ : Matrix m m R)ᴴ = permOp σ⁻¹ := by
  ext x y
  simp only [conjTranspose_apply, permOp_apply]
  by_cases h : y = σ x
  · subst h
    simp
  · have hx : ¬x = σ.symm y := fun hx => h (by rw [hx]; simp)
    simp [h, hx]

end PermOp

section PermOpUnitary

variable [DecidableEq m] [Fintype m] [CommRing R] [StarRing R]

theorem permOp_mem_unitaryGroup (σ : Equiv.Perm m) :
    (permOp σ : Matrix m m R) ∈ unitaryGroup m R := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, permOp_conjTranspose, permOp_mul,
    mul_inv_cancel, permOp_one]

end PermOpUnitary

end

end TheoremOS.LinearAlgebra
