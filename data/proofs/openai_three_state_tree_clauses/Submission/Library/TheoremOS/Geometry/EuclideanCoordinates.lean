import Mathlib

/-!
# Coordinates in `EuclideanSpace ℝ ι`

Coordinate forms of the norm, inner product and distance of `EuclideanSpace ℝ ι`, for a point
`x` (`x i` is its `i`-th coordinate) and for a vector built as `WithLp.toLp 2 f` or `!₂[a, b, …]`.
Contents: `‖x‖ = √(∑ x i²)`, `⟪x, y⟫ = ∑ x i * y i`, `dist x y ^ 2 = ∑ (x i - y i)²`; spheres and
balls about any center as `∑ (x i - c i)² = r²` (`≤`, `<`); `‖x‖ = r` as `∑ x i² = r²`; the
expansion `x = ∑ i, x i • single i 1` and `toLp 2 f = ∑ i, f i • single i 1`; product index types
`ι × κ` as a double sum; the two- and three-dimensional cases written out; transposes as adjoints,
`⟪toLp (A *ᵥ x), y⟫ = ⟪x, toLp (Aᵀ *ᵥ y)⟫`, and orthogonal matrices (`Matrix.orthogonalGroup`)
as isometries: they preserve inner products, norms and distances.

Sources: S. Axler, *Linear Algebra Done Right*, 3rd ed., Springer, 2015, Chapter 6 (inner
products on `𝐑ⁿ`, orthonormal bases) and §7.C (isometries); Mathlib's `EuclideanSpace` API, of
which this is a thin layer. Textbook material; nothing here is specific to a benchmark problem.

Bridges: `!₂[a, b]` is notation for `WithLp.toLp 2 ![a, b]`, so the `toLp` lemmas apply to it, and
the `_fin_two`/`_fin_three` lemmas evaluate `![a, b] 0` etc. A point is applied directly,
`x i`, and `x.ofLp` is the underlying function (`PiLp.toLp_apply`, `WithLp.ofLp_toLp` are `rfl`).
For `U : Matrix.orthogonalGroup ι ℝ` pass `U.property`; `*ᵥ` needs `open Matrix`.
Mathlib already has `EuclideanSpace.norm_eq`, `real_norm_sq_eq`, `dist_eq`, `ball_zero_eq`,
`sphere_zero_eq`, `inner_single_left`, `volume_ball` and `volume_ball_fin_two`; coordinate
Cauchy–Schwarz is `Finset.inner_mul_le_norm_mul_norm` and `Finset.sum_mul_sq_le_sq_mul_sq`.
-/

namespace TheoremOS.Geometry

open Finset Matrix WithLp
open scoped BigOperators RealInnerProductSpace

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

section Coordinates

lemma norm_eq_sqrt_sum (x : EuclideanSpace ℝ ι) : ‖x‖ = √(∑ i, x i ^ 2) := by
  rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg x)]

lemma inner_eq_sum (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma dist_sq_eq_sum (x y : EuclideanSpace ℝ ι) : dist x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp only [EuclideanSpace.dist_sq_eq, Real.dist_eq, sq_abs]

lemma dist_eq_sqrt_sum (x y : EuclideanSpace ℝ ι) : dist x y = √(∑ i, (x i - y i) ^ 2) := by
  rw [← dist_sq_eq_sum, Real.sqrt_sq dist_nonneg]

lemma mem_sphere_iff_sum {x c : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ Metric.sphere c r ↔ ∑ i, (x i - c i) ^ 2 = r ^ 2 := by
  rw [Metric.mem_sphere, ← dist_sq_eq_sum, sq_eq_sq₀ dist_nonneg hr]

lemma mem_closedBall_iff_sum {x c : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ Metric.closedBall c r ↔ ∑ i, (x i - c i) ^ 2 ≤ r ^ 2 := by
  rw [Metric.mem_closedBall, ← dist_sq_eq_sum, sq_le_sq₀ dist_nonneg hr]

lemma mem_ball_iff_sum {x c : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    x ∈ Metric.ball c r ↔ ∑ i, (x i - c i) ^ 2 < r ^ 2 := by
  rw [Metric.mem_ball, ← dist_sq_eq_sum, sq_lt_sq₀ dist_nonneg hr]

lemma norm_eq_iff_sum {x : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ = r ↔ ∑ i, x i ^ 2 = r ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq, sq_eq_sq₀ (norm_nonneg x) hr]

lemma norm_le_iff_sum {x : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ ≤ r ↔ ∑ i, x i ^ 2 ≤ r ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq, sq_le_sq₀ (norm_nonneg x) hr]

lemma norm_lt_iff_sum {x : EuclideanSpace ℝ ι} {r : ℝ} (hr : 0 ≤ r) :
    ‖x‖ < r ↔ ∑ i, x i ^ 2 < r ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq, sq_lt_sq₀ (norm_nonneg x) hr]

lemma norm_eq_one_iff_sum {x : EuclideanSpace ℝ ι} : ‖x‖ = 1 ↔ ∑ i, x i ^ 2 = 1 := by
  rw [norm_eq_iff_sum zero_le_one, one_pow]

end Coordinates

section ToLp

lemma norm_sq_toLp_eq_sum (f : ι → ℝ) : ‖(toLp 2 f : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, f i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq _

lemma norm_toLp_eq_sqrt_sum (f : ι → ℝ) : ‖(toLp 2 f : EuclideanSpace ℝ ι)‖ = √(∑ i, f i ^ 2) :=
  norm_eq_sqrt_sum _

lemma inner_toLp_eq_sum (f g : ι → ℝ) :
    ⟪(toLp 2 f : EuclideanSpace ℝ ι), toLp 2 g⟫ = ∑ i, f i * g i :=
  inner_eq_sum _ _

lemma dist_sq_toLp_eq_sum (f g : ι → ℝ) :
    dist (toLp 2 f : EuclideanSpace ℝ ι) (toLp 2 g) ^ 2 = ∑ i, (f i - g i) ^ 2 :=
  dist_sq_eq_sum _ _

lemma dist_toLp_eq_sqrt_sum (f g : ι → ℝ) :
    dist (toLp 2 f : EuclideanSpace ℝ ι) (toLp 2 g) = √(∑ i, (f i - g i) ^ 2) :=
  dist_eq_sqrt_sum _ _

/-- A point is the sum of its coordinates along the standard basis. -/
lemma sum_smul_single_eq [DecidableEq ι] (x : EuclideanSpace ℝ ι) :
    ∑ i, x i • EuclideanSpace.single i (1 : ℝ) = x := by
  ext j
  simp [Pi.single_apply]

lemma toLp_eq_sum_smul_single [DecidableEq ι] (f : ι → ℝ) :
    (toLp 2 f : EuclideanSpace ℝ ι) = ∑ i, f i • EuclideanSpace.single i (1 : ℝ) :=
  (sum_smul_single_eq _).symm

lemma inner_single_single [DecidableEq ι] (i j : ι) (a b : ℝ) :
    ⟪EuclideanSpace.single i a, EuclideanSpace.single j b⟫ = if i = j then a * b else 0 := by
  rw [EuclideanSpace.inner_single_left]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- On a product index type the squared norm is a double sum. -/
lemma norm_sq_prod_eq_sum (x : EuclideanSpace ℝ (ι × κ)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, x (i, j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]

end ToLp

section LowDimension

lemma norm_sq_fin_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma norm_fin_two (x : EuclideanSpace ℝ (Fin 2)) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [← norm_sq_fin_two, Real.sqrt_sq (norm_nonneg x)]

lemma inner_fin_two (x y : EuclideanSpace ℝ (Fin 2)) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  rw [inner_eq_sum, Fin.sum_univ_two]

lemma dist_sq_fin_two (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [dist_sq_eq_sum, Fin.sum_univ_two]

lemma dist_fin_two (x y : EuclideanSpace ℝ (Fin 2)) :
    dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [← dist_sq_fin_two, Real.sqrt_sq dist_nonneg]

lemma norm_sq_fin_three (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

lemma norm_fin_three (x : EuclideanSpace ℝ (Fin 3)) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rw [← norm_sq_fin_three, Real.sqrt_sq (norm_nonneg x)]

lemma inner_fin_three (x y : EuclideanSpace ℝ (Fin 3)) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [inner_eq_sum, Fin.sum_univ_three]

lemma dist_sq_fin_three (x y : EuclideanSpace ℝ (Fin 3)) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 := by
  rw [dist_sq_eq_sum, Fin.sum_univ_three]

lemma dist_fin_three (x y : EuclideanSpace ℝ (Fin 3)) :
    dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) := by
  rw [← dist_sq_fin_three, Real.sqrt_sq dist_nonneg]

lemma eq_vec_fin_two (x : EuclideanSpace ℝ (Fin 2)) : x = !₂[x 0, x 1] := by
  ext i
  fin_cases i <;> rfl

lemma eq_vec_fin_three (x : EuclideanSpace ℝ (Fin 3)) : x = !₂[x 0, x 1, x 2] := by
  ext i
  fin_cases i <;> rfl

lemma norm_sq_vec_two (a b : ℝ) : ‖!₂[a, b]‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_sq_fin_two]; rfl

lemma norm_vec_two (a b : ℝ) : ‖!₂[a, b]‖ = √(a ^ 2 + b ^ 2) := by
  rw [norm_fin_two]; rfl

lemma inner_vec_two (a b c d : ℝ) : ⟪!₂[a, b], !₂[c, d]⟫ = a * c + b * d := by
  rw [inner_fin_two]; rfl

lemma dist_sq_vec_two (a b c d : ℝ) : dist !₂[a, b] !₂[c, d] ^ 2 = (a - c) ^ 2 + (b - d) ^ 2 := by
  rw [dist_sq_fin_two]; rfl

lemma dist_vec_two (a b c d : ℝ) : dist !₂[a, b] !₂[c, d] = √((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [dist_fin_two]; rfl

lemma norm_sq_vec_three (a b c : ℝ) : ‖!₂[a, b, c]‖ ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 := by
  rw [norm_sq_fin_three]; rfl

lemma norm_vec_three (a b c : ℝ) : ‖!₂[a, b, c]‖ = √(a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [norm_fin_three]; rfl

lemma inner_vec_three (a b c d e f : ℝ) :
    ⟪!₂[a, b, c], !₂[d, e, f]⟫ = a * d + b * e + c * f := by
  rw [inner_fin_three]; rfl

lemma dist_sq_vec_three (a b c d e f : ℝ) :
    dist !₂[a, b, c] !₂[d, e, f] ^ 2 = (a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2 := by
  rw [dist_sq_fin_three]; rfl

lemma dist_vec_three (a b c d e f : ℝ) :
    dist !₂[a, b, c] !₂[d, e, f] = √((a - d) ^ 2 + (b - e) ^ 2 + (c - f) ^ 2) := by
  rw [dist_fin_three]; rfl

end LowDimension

section Orthogonal

/-- The transpose is the adjoint: `⟪A x, y⟫ = ⟪x, Aᵀ y⟫`. -/
lemma inner_toLp_mulVec (A : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    ⟪(toLp 2 (A *ᵥ ofLp x) : EuclideanSpace ℝ κ), y⟫ =
      ⟪x, (toLp 2 (Aᵀ *ᵥ ofLp y) : EuclideanSpace ℝ ι)⟫ := by
  rw [inner_eq_sum, inner_eq_sum]
  change (A *ᵥ ofLp x) ⬝ᵥ ofLp y = ofLp x ⬝ᵥ (Aᵀ *ᵥ ofLp y)
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

variable [DecidableEq ι] {U : Matrix ι ι ℝ}

/-- An orthogonal matrix preserves inner products. -/
theorem inner_toLp_mulVec_of_mem_orthogonalGroup (hU : U ∈ Matrix.orthogonalGroup ι ℝ)
    (x y : EuclideanSpace ℝ ι) :
    ⟪(toLp 2 (U *ᵥ ofLp x) : EuclideanSpace ℝ ι), toLp 2 (U *ᵥ ofLp y)⟫ = ⟪x, y⟫ := by
  rw [inner_toLp_mulVec, ofLp_toLp, Matrix.mulVec_mulVec,
    (Matrix.mem_orthogonalGroup_iff' ι ℝ).1 hU, Matrix.one_mulVec, toLp_ofLp]

/-- An orthogonal matrix preserves norms. -/
theorem norm_toLp_mulVec_of_mem_orthogonalGroup (hU : U ∈ Matrix.orthogonalGroup ι ℝ)
    (x : EuclideanSpace ℝ ι) : ‖(toLp 2 (U *ᵥ ofLp x) : EuclideanSpace ℝ ι)‖ = ‖x‖ := by
  have h := inner_toLp_mulVec_of_mem_orthogonalGroup hU x x
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- An orthogonal matrix preserves distances. -/
theorem dist_toLp_mulVec_of_mem_orthogonalGroup (hU : U ∈ Matrix.orthogonalGroup ι ℝ)
    (x y : EuclideanSpace ℝ ι) :
    dist (toLp 2 (U *ᵥ ofLp x) : EuclideanSpace ℝ ι) (toLp 2 (U *ᵥ ofLp y)) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← toLp_sub, ← Matrix.mulVec_sub, ← ofLp_sub,
    norm_toLp_mulVec_of_mem_orthogonalGroup hU]

end Orthogonal

end

end TheoremOS.Geometry
