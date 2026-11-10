import Mathlib

/-!
# Distortion of finite metric embeddings and Poincaré inequalities

For a finite set `X` with a distance function `ρ : X → X → ℝ` and a map `f` into a pseudometric
space, `maxExpansion ρ f = sup_{x ≠ y} d(fx, fy) / ρ(x, y)`, `maxContraction ρ f =
sup_{x ≠ y} ρ(x, y) / d(fx, fy)` and `embeddingDistortion ρ f` is their product. Contents: bounded
suprema and the pointwise bounds `d ≤ s ρ`, `ρ ≤ r d`; upper bounds from Lipschitz bounds; lower
bounds from two test pairs and `1 ≤ distortion`; the Poincaré method
(`sum_mul_pow_le_embeddingDistortion_pow`): if `∑ a(x,y) d(fx,fy)^q ≤ K ∑ b(x,y) d(fx,fy)^q`
holds for the map `f`, then `∑ a ρ^q ≤ K D^q ∑ b ρ^q` with `D` its distortion; transfer of a
scalar inequality `∑ a |gx - gy| ≤ K ∑ b |gx - gy|` (all `g : X → ℝ`) to maps into `ℓ¹`
(`lp (fun _ : ℕ => ℝ) 1`) and into `PiLp 1`, and of the squared form to `EuclideanSpace` and `ℓ²`;
injective maps of a countable set into `ℓᵖ`; `finToLpOne`, the isometric copy of
`(Fin m → ℝ, ∑ |·|)` inside `ℓ¹`.

Sources: J. Matoušek, *Lectures on Discrete Geometry*, Springer GTM 212, 2002, Chapter 15
(15.1 distortion, 15.4 Poincaré inequalities and lower bounds, 15.5 ℓ₁ via cut metrics);
N. Linial, E. London and Y. Rabinovich, The geometry of graphs and some of its algorithmic
applications, Combinatorica 15 (1995) 215–245, Section 3; P. Enflo, On the nonexistence of uniform
homeomorphisms between Lp-spaces, Ark. Mat. 8 (1969) 103–105. Textbook material; nothing here is
specific to a benchmark problem.

Bridges: a distortion written as
`sSup {r | ∃ x y, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} * sSup {r | ∃ x y, x ≠ y ∧ r = ρ x y / ‖f x - f y‖}`
is `embeddingDistortion ρ f` by `embeddingDistortion_eq_norm`; on a subtype of words with
`ρ x y = (ed x.val y.val : ℝ)` it is the same statement with that `ρ`. A least distortion
`sInf {D | ∃ f, Injective f ∧ D = embeddingDistortion ρ f}` is bounded below with `le_csInf`,
nonemptiness coming from `exists_injective_lp`. A map `F : X → Fin m → ℝ` with bounds on
`∑ i, |F x i - F y i|` gives `fun x => finToLpOne (F x)` with `norm_finToLpOne_sub`.
-/

namespace TheoremOS.Analysis

open Finset

noncomputable section

variable {X : Type*} {Y : Type*} [PseudoMetricSpace Y]

/-- The largest ratio `d(fx, fy) / ρ(x, y)` over distinct pairs. -/
def maxExpansion (ρ : X → X → ℝ) (f : X → Y) : ℝ :=
  sSup {r | ∃ x y : X, x ≠ y ∧ r = dist (f x) (f y) / ρ x y}

/-- The largest ratio `ρ(x, y) / d(fx, fy)` over distinct pairs. -/
def maxContraction (ρ : X → X → ℝ) (f : X → Y) : ℝ :=
  sSup {r | ∃ x y : X, x ≠ y ∧ r = ρ x y / dist (f x) (f y)}

/-- Distortion: the product of the largest expansion and the largest contraction. -/
def embeddingDistortion (ρ : X → X → ℝ) (f : X → Y) : ℝ :=
  maxExpansion ρ f * maxContraction ρ f

theorem embeddingDistortion_eq_norm {E : Type*} [SeminormedAddCommGroup E] (ρ : X → X → ℝ)
    (f : X → E) :
    embeddingDistortion ρ f =
      sSup {r | ∃ x y : X, x ≠ y ∧ r = ‖f x - f y‖ / ρ x y} *
        sSup {r | ∃ x y : X, x ≠ y ∧ r = ρ x y / ‖f x - f y‖} := by
  simp only [embeddingDistortion, maxExpansion, maxContraction, dist_eq_norm]

section Bounds

variable [Finite X] (ρ : X → X → ℝ) (f : X → Y)

theorem bddAbove_expansion :
    BddAbove {r | ∃ x y : X, x ≠ y ∧ r = dist (f x) (f y) / ρ x y} :=
  (Set.finite_range fun p : X × X => dist (f p.1) (f p.2) / ρ p.1 p.2).bddAbove.mono
    (by rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩)

theorem bddAbove_contraction :
    BddAbove {r | ∃ x y : X, x ≠ y ∧ r = ρ x y / dist (f x) (f y)} :=
  (Set.finite_range fun p : X × X => ρ p.1 p.2 / dist (f p.1) (f p.2)).bddAbove.mono
    (by rintro r ⟨x, y, -, rfl⟩; exact ⟨(x, y), rfl⟩)

variable {ρ f}

theorem div_le_maxExpansion {x y : X} (h : x ≠ y) :
    dist (f x) (f y) / ρ x y ≤ maxExpansion ρ f :=
  le_csSup (bddAbove_expansion ρ f) ⟨x, y, h, rfl⟩

theorem div_le_maxContraction {x y : X} (h : x ≠ y) :
    ρ x y / dist (f x) (f y) ≤ maxContraction ρ f :=
  le_csSup (bddAbove_contraction ρ f) ⟨x, y, h, rfl⟩

/-- `d(fx, fy) ≤ s ρ(x, y)` with `s` the largest expansion. -/
theorem dist_le_maxExpansion_mul {x y : X} (h : x ≠ y) (hρ : 0 < ρ x y) :
    dist (f x) (f y) ≤ maxExpansion ρ f * ρ x y :=
  (div_le_iff₀ hρ).mp (div_le_maxExpansion h)

/-- `ρ(x, y) ≤ r d(fx, fy)` with `r` the largest contraction. -/
theorem le_maxContraction_mul_dist {x y : X} (h : x ≠ y) (hd : 0 < dist (f x) (f y)) :
    ρ x y ≤ maxContraction ρ f * dist (f x) (f y) :=
  (div_le_iff₀ hd).mp (div_le_maxContraction h)

end Bounds

variable {ρ : X → X → ℝ} {f : X → Y}

theorem maxExpansion_nonneg (hρ : ∀ x y, x ≠ y → 0 ≤ ρ x y) : 0 ≤ maxExpansion ρ f :=
  Real.sSup_nonneg (by rintro r ⟨x, y, hxy, rfl⟩; exact div_nonneg dist_nonneg (hρ x y hxy))

theorem maxContraction_nonneg (hρ : ∀ x y, x ≠ y → 0 ≤ ρ x y) : 0 ≤ maxContraction ρ f :=
  Real.sSup_nonneg (by rintro r ⟨x, y, hxy, rfl⟩; exact div_nonneg (hρ x y hxy) dist_nonneg)

theorem embeddingDistortion_nonneg (hρ : ∀ x y, x ≠ y → 0 ≤ ρ x y) :
    0 ≤ embeddingDistortion ρ f :=
  mul_nonneg (maxExpansion_nonneg hρ) (maxContraction_nonneg hρ)

/-- Lipschitz upper bound `d(fx, fy) ≤ s ρ(x, y)` gives `maxExpansion ≤ s`. -/
theorem maxExpansion_le {s : ℝ} (hs : 0 ≤ s) (hρ : ∀ x y, x ≠ y → 0 < ρ x y)
    (h : ∀ x y, x ≠ y → dist (f x) (f y) ≤ s * ρ x y) : maxExpansion ρ f ≤ s :=
  Real.sSup_le (by rintro r ⟨x, y, hxy, rfl⟩; exact div_le_of_le_mul₀ (hρ x y hxy).le hs (h x y hxy))
    hs

/-- Co-Lipschitz bound `ρ(x, y) ≤ r d(fx, fy)` gives `maxContraction ≤ r`. -/
theorem maxContraction_le {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ x y, x ≠ y → ρ x y ≤ r * dist (f x) (f y)) : maxContraction ρ f ≤ r :=
  Real.sSup_le (by rintro c ⟨x, y, hxy, rfl⟩; exact div_le_of_le_mul₀ dist_nonneg hr (h x y hxy)) hr

theorem embeddingDistortion_le {s r : ℝ} (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hρ : ∀ x y, x ≠ y → 0 < ρ x y)
    (hup : ∀ x y, x ≠ y → dist (f x) (f y) ≤ s * ρ x y)
    (hlow : ∀ x y, x ≠ y → ρ x y ≤ r * dist (f x) (f y)) :
    embeddingDistortion ρ f ≤ s * r :=
  mul_le_mul (maxExpansion_le hs hρ hup) (maxContraction_le hr hlow)
    (maxContraction_nonneg fun x y h => (hρ x y h).le) hs

/-- Two test pairs: the expansion of one pair times the contraction of another. -/
theorem div_mul_div_le_embeddingDistortion [Finite X] (hρ : ∀ x y, x ≠ y → 0 ≤ ρ x y)
    {x y x' y' : X} (hxy : x ≠ y) (hxy' : x' ≠ y') :
    dist (f x) (f y) / ρ x y * (ρ x' y' / dist (f x') (f y')) ≤ embeddingDistortion ρ f :=
  mul_le_mul (div_le_maxExpansion hxy) (div_le_maxContraction hxy')
    (div_nonneg (hρ x' y' hxy') dist_nonneg) (maxExpansion_nonneg hρ)

/-- A finite set with two points and an injective map has distortion at least `1`. -/
theorem one_le_embeddingDistortion [Finite X] (hρ : ∀ x y, x ≠ y → 0 < ρ x y)
    (hf : ∀ x y, x ≠ y → 0 < dist (f x) (f y)) {x y : X} (hxy : x ≠ y) :
    1 ≤ embeddingDistortion ρ f := by
  have h := div_mul_div_le_embeddingDistortion (f := f) (fun a b h => (hρ a b h).le) hxy hxy
  have h1 : dist (f x) (f y) / ρ x y * (ρ x y / dist (f x) (f y)) = 1 := by
    field_simp [(hρ x y hxy).ne', (hf x y hxy).ne']
  linarith

/-- The Poincaré method. If the map satisfies `∑ a d^q ≤ K ∑ b d^q` (`d = d(fx, fy)`), then the
same inequality holds for `ρ` with the loss `D^q`, `D` the distortion. -/
theorem sum_mul_pow_le_embeddingDistortion_pow [Fintype X] (q : ℕ) {a b : X → X → ℝ} {K : ℝ}
    (ha : ∀ x y, 0 ≤ a x y) (hb : ∀ x y, 0 ≤ b x y) (hK : 0 ≤ K)
    (hρ0 : ∀ x, ρ x x = 0) (hρ : ∀ x y, x ≠ y → 0 < ρ x y)
    (hf : ∀ x y, x ≠ y → 0 < dist (f x) (f y))
    (hP : ∑ x, ∑ y, a x y * dist (f x) (f y) ^ q ≤ K * ∑ x, ∑ y, b x y * dist (f x) (f y) ^ q) :
    ∑ x, ∑ y, a x y * ρ x y ^ q ≤
      K * embeddingDistortion ρ f ^ q * ∑ x, ∑ y, b x y * ρ x y ^ q := by
  have hρnn : ∀ x y, x ≠ y → 0 ≤ ρ x y := fun x y h => (hρ x y h).le
  have hs := maxExpansion_nonneg (f := f) hρnn
  have hr := maxContraction_nonneg (f := f) hρnn
  have h1 : ∀ x y, a x y * ρ x y ^ q ≤
      maxContraction ρ f ^ q * (a x y * dist (f x) (f y) ^ q) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · simp [hρ0, zero_pow hq.ne']
    · have := le_maxContraction_mul_dist (ρ := ρ) (f := f) hxy (hf x y hxy)
      calc a x y * ρ x y ^ q ≤ a x y * (maxContraction ρ f * dist (f x) (f y)) ^ q :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hρ x y hxy).le this q) (ha x y)
        _ = _ := by ring
  have h2 : ∀ x y, b x y * dist (f x) (f y) ^ q ≤
      maxExpansion ρ f ^ q * (b x y * ρ x y ^ q) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rcases Nat.eq_zero_or_pos q with rfl | hq
      · simp
      · simp [hρ0, zero_pow hq.ne']
    · have := dist_le_maxExpansion_mul (ρ := ρ) (f := f) hxy (hρ x y hxy)
      calc b x y * dist (f x) (f y) ^ q ≤ b x y * (maxExpansion ρ f * ρ x y) ^ q :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dist_nonneg this q) (hb x y)
        _ = _ := by ring
  have hA : ∑ x, ∑ y, a x y * ρ x y ^ q ≤
      maxContraction ρ f ^ q * ∑ x, ∑ y, a x y * dist (f x) (f y) ^ q := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => h1 x y
  have hB : ∑ x, ∑ y, b x y * dist (f x) (f y) ^ q ≤
      maxExpansion ρ f ^ q * ∑ x, ∑ y, b x y * ρ x y ^ q := by
    simp only [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => h2 x y
  calc ∑ x, ∑ y, a x y * ρ x y ^ q
      ≤ maxContraction ρ f ^ q * ∑ x, ∑ y, a x y * dist (f x) (f y) ^ q := hA
    _ ≤ maxContraction ρ f ^ q * (K * ∑ x, ∑ y, b x y * dist (f x) (f y) ^ q) :=
        mul_le_mul_of_nonneg_left hP (pow_nonneg hr q)
    _ ≤ maxContraction ρ f ^ q * (K * (maxExpansion ρ f ^ q * ∑ x, ∑ y, b x y * ρ x y ^ q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hK) (pow_nonneg hr q)
    _ = K * embeddingDistortion ρ f ^ q * ∑ x, ∑ y, b x y * ρ x y ^ q := by
        rw [embeddingDistortion, mul_pow]
        ring

section Transfer

variable [Fintype X]

/-- Summing a coordinatewise inequality over a summable family of coordinates. -/
theorem sum_sum_tsum_le {a b : X → X → ℝ} {K : ℝ} (u : X → X → ℕ → ℝ)
    (hu : ∀ x y, Summable (u x y))
    (h : ∀ i, ∑ x, ∑ y, a x y * u x y i ≤ K * ∑ x, ∑ y, b x y * u x y i) :
    ∑ x, ∑ y, a x y * ∑' i, u x y i ≤ K * ∑ x, ∑ y, b x y * ∑' i, u x y i := by
  have key : ∀ c : X → X → ℝ,
      ∑ x, ∑ y, c x y * ∑' i, u x y i = ∑' i, ∑ x, ∑ y, c x y * u x y i := by
    intro c
    rw [Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => (hu x y).mul_left _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Summable.tsum_finsetSum fun y _ => (hu x y).mul_left _]
    exact Finset.sum_congr rfl fun y _ => ((hu x y).tsum_mul_left _).symm
  rw [key a, key b, ← ((summable_sum fun x _ => summable_sum fun y _ =>
    (hu x y).mul_left (b x y)).tsum_mul_left K)]
  exact Summable.tsum_le_tsum h (summable_sum fun x _ => summable_sum fun y _ =>
    (hu x y).mul_left _) ((summable_sum fun x _ => summable_sum fun y _ =>
    (hu x y).mul_left _).mul_left K)

theorem norm_lpOne_eq_tsum (v : lp (fun _ : ℕ => ℝ) 1) : ‖v‖ = ∑' i, |v i| := by
  have := lp.norm_eq_tsum_rpow (p := 1) (by simp) v
  simpa [Real.norm_eq_abs] using this

theorem summable_abs_lpOne (v : lp (fun _ : ℕ => ℝ) 1) : Summable fun i => |v i| := by
  have := (lp.memℓp v).summable (p := 1) (by simp)
  simpa [Real.norm_eq_abs] using this

/-- ℓ¹ transfer: a Poincaré inequality for real functions holds for `ℓ¹`-valued maps. -/
theorem poincare_lpOne {a b : X → X → ℝ} {K : ℝ}
    (h : ∀ g : X → ℝ, ∑ x, ∑ y, a x y * |g x - g y| ≤ K * ∑ x, ∑ y, b x y * |g x - g y|)
    (F : X → lp (fun _ : ℕ => ℝ) 1) :
    ∑ x, ∑ y, a x y * ‖F x - F y‖ ≤ K * ∑ x, ∑ y, b x y * ‖F x - F y‖ := by
  simp only [norm_lpOne_eq_tsum, lp.coeFn_sub, Pi.sub_apply]
  exact sum_sum_tsum_le (fun x y i => |F x i - F y i|)
    (fun x y => by simpa [lp.coeFn_sub] using summable_abs_lpOne (F x - F y))
    fun i => h fun x => F x i

/-- Finite-dimensional ℓ¹ transfer. -/
theorem poincare_piLpOne {ι : Type*} [Fintype ι] {a b : X → X → ℝ} {K : ℝ}
    (h : ∀ g : X → ℝ, ∑ x, ∑ y, a x y * |g x - g y| ≤ K * ∑ x, ∑ y, b x y * |g x - g y|)
    (F : X → PiLp 1 (fun _ : ι => ℝ)) :
    ∑ x, ∑ y, a x y * ‖F x - F y‖ ≤ K * ∑ x, ∑ y, b x y * ‖F x - F y‖ := by
  have key : ∀ c : X → X → ℝ, ∑ x, ∑ y, c x y * ‖F x - F y‖ =
      ∑ i, ∑ x, ∑ y, c x y * |(F x).ofLp i - (F y).ofLp i| := by
    intro c
    simp only [PiLp.norm_eq_of_L1, PiLp.sub_apply, Real.norm_eq_abs, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
  rw [key a, key b, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h fun x => (F x).ofLp i

/-- Euclidean transfer of a squared Poincaré inequality (Enflo type). -/
theorem poincare_euclidean_sq {ι : Type*} [Fintype ι] {a b : X → X → ℝ} {K : ℝ}
    (h : ∀ g : X → ℝ, ∑ x, ∑ y, a x y * (g x - g y) ^ 2 ≤ K * ∑ x, ∑ y, b x y * (g x - g y) ^ 2)
    (F : X → EuclideanSpace ℝ ι) :
    ∑ x, ∑ y, a x y * ‖F x - F y‖ ^ 2 ≤ K * ∑ x, ∑ y, b x y * ‖F x - F y‖ ^ 2 := by
  have key : ∀ c : X → X → ℝ, ∑ x, ∑ y, c x y * ‖F x - F y‖ ^ 2 =
      ∑ i, ∑ x, ∑ y, c x y * ((F x).ofLp i - (F y).ofLp i) ^ 2 := by
    intro c
    simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans Finset.sum_comm
  rw [key a, key b, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => h fun x => (F x).ofLp i

theorem norm_sq_lpTwo_eq_tsum (v : lp (fun _ : ℕ => ℝ) 2) : ‖v‖ ^ 2 = ∑' i, v i ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by simp) v
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem summable_sq_lpTwo (v : lp (fun _ : ℕ => ℝ) 2) : Summable fun i => v i ^ 2 := by
  have := (lp.memℓp v).summable (p := 2) (by simp)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- ℓ² transfer of a squared Poincaré inequality. -/
theorem poincare_lpTwo_sq {a b : X → X → ℝ} {K : ℝ}
    (h : ∀ g : X → ℝ, ∑ x, ∑ y, a x y * (g x - g y) ^ 2 ≤ K * ∑ x, ∑ y, b x y * (g x - g y) ^ 2)
    (F : X → lp (fun _ : ℕ => ℝ) 2) :
    ∑ x, ∑ y, a x y * ‖F x - F y‖ ^ 2 ≤ K * ∑ x, ∑ y, b x y * ‖F x - F y‖ ^ 2 := by
  simp only [norm_sq_lpTwo_eq_tsum, lp.coeFn_sub, Pi.sub_apply]
  exact sum_sum_tsum_le (fun x y i => (F x i - F y i) ^ 2)
    (fun x y => by simpa [lp.coeFn_sub] using summable_sq_lpTwo (F x - F y))
    fun i => h fun x => F x i

end Transfer

/-- A countable set has injective maps into every `ℓᵖ`, so least distortions are infima over
nonempty sets. -/
theorem exists_injective_lp (X : Type*) [Countable X] (p : ENNReal) :
    ∃ F : X → lp (fun _ : ℕ => ℝ) p, Function.Injective F := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat X
  refine ⟨fun x => lp.single p (e x) (1 : ℝ), fun x y hxy => he ?_⟩
  have := congrArg (fun v : lp (fun _ : ℕ => ℝ) p => v (e x)) hxy
  by_contra hne
  simp [lp.single_apply, Ne.symm hne] at this

/-- The finite vector `v`, padded with zeros, as an element of `ℓ¹`. -/
def finToLpOne {m : ℕ} (v : Fin m → ℝ) : lp (fun _ : ℕ => ℝ) 1 :=
  ⟨fun i => if h : i < m then v ⟨i, h⟩ else 0, by
    refine Memℓp.of_exponent_ge (memℓp_zero ((Set.finite_lt_nat m).subset ?_)) bot_le
    intro i hi
    by_contra h
    have h' : ¬ i < m := h
    exact hi (by simp [h'])⟩

@[simp] theorem finToLpOne_apply {m : ℕ} (v : Fin m → ℝ) (i : ℕ) :
    finToLpOne v i = if h : i < m then v ⟨i, h⟩ else 0 := rfl

/-- `‖finToLpOne v - finToLpOne w‖ = ∑ i, |v i - w i|`. -/
theorem norm_finToLpOne_sub {m : ℕ} (v w : Fin m → ℝ) :
    ‖finToLpOne v - finToLpOne w‖ = ∑ i, |v i - w i| := by
  rw [norm_lpOne_eq_tsum, tsum_eq_sum (s := Finset.range m)]
  · rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  · intro i hi
    have : ¬ i < m := by simpa using hi
    simp [this]

theorem finToLpOne_injective {m : ℕ} : Function.Injective (finToLpOne (m := m)) := by
  intro v w h
  funext i
  have := congrArg (fun u : lp (fun _ : ℕ => ℝ) 1 => u i.val) h
  simpa using this

end

end TheoremOS.Analysis
