import Mathlib

namespace OAI

/-! Existence of the fixed-length forced free energy of honeycomb walks. -/

noncomputable section
open scoped ENNReal Topology
open Filter

namespace HoneycombForce

structure Vertex where
  col : ℤ
  row : ℤ
  up : Bool
  deriving DecidableEq

def up (i j : ℤ) : Vertex := ⟨i, j, true⟩

def down (i j : ℤ) : Vertex := ⟨i, j, false⟩

def rowSpacing : ℝ := Real.sqrt 3 / 2

def position (v : Vertex) : ℂ :=
  if v.up then
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1/2,
      rowSpacing * ((v.row : ℝ) + 1/3)⟩
  else
    ⟨(v.col : ℝ) + (v.row : ℝ) / 2 + 1,
      rowSpacing * ((v.row : ℝ) + 2/3)⟩

def rho : ℝ := (Real.sqrt (2 + Real.sqrt 2))⁻¹

def neighbors (v : Vertex) : Finset Vertex :=
  if v.up then
    {down v.col (v.row-1), down v.col v.row, down (v.col-1) v.row}
  else
    {up v.col (v.row+1), up v.col v.row, up (v.col+1) v.row}

def walkLists (o : Vertex) : ℕ → Finset (List Vertex)
  | 0 => {[o]}
  | n+1 => (neighbors o).biUnion (fun v => (walkLists v n).image (List.cons o))

lemma mem_walkLists_iff {o : Vertex} {n : ℕ} {γ : List Vertex} :
    γ ∈ walkLists o n ↔
      γ.head? = some o ∧ γ.length = n + 1 ∧
        List.IsChain (fun a b : Vertex => b ∈ neighbors a) γ := by
  induction n generalizing o γ with
  | zero =>
      constructor
      · intro hγ
        rw [show walkLists o 0 = ({[o]} : Finset (List Vertex)) from rfl] at hγ
        simp only [Finset.mem_singleton] at hγ
        subst γ
        exact ⟨rfl, rfl, List.isChain_singleton _⟩
      · rintro ⟨hhead, hlen, _⟩
        cases γ with
        | nil => simp at hhead
        | cons a t =>
            simp only [List.head?_cons, Option.some_inj] at hhead
            have htlen : t.length = 0 := by simpa using hlen
            have ht : t = [] := List.length_eq_zero_iff.mp htlen
            subst a
            subst t
            rw [show walkLists o 0 = ({[o]} : Finset (List Vertex)) from rfl]
            simp
  | succ n ih =>
      change γ ∈ (neighbors o).biUnion
          (fun v => (walkLists v n).image (List.cons o)) ↔ _
      simp only [Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨v, hv, δ, hδ, rfl⟩
        obtain ⟨hhead, hlen, hchain⟩ := (ih (o := v) (γ := δ)).1 hδ
        refine ⟨rfl, ?_, ?_⟩
        · simp [hlen]
        · rw [List.isChain_cons]
          refine ⟨?_, hchain⟩
          intro y hy
          have hy' : y = v := by simpa [hhead] using hy.symm
          subst y
          exact hv
      · rintro ⟨hhead, hlen, hchain⟩
        cases γ with
        | nil => simp at hhead
        | cons a t =>
            simp only [List.head?_cons, Option.some_inj] at hhead
            subst a
            simp only [List.length_cons] at hlen
            obtain ⟨hrel, hchain'⟩ := List.isChain_cons.mp hchain
            cases t with
            | nil => simp at hlen
            | cons v t' =>
                have hv : v ∈ neighbors o := hrel v (by simp [List.head?_cons])
                have hδlen : (v :: t').length = n + 1 := by simpa using hlen
                have hδ : v :: t' ∈ walkLists v n :=
                  (ih (o := v) (γ := v :: t')).2 ⟨rfl, hδlen, hchain'⟩
                exact ⟨v, hv, v :: t', hδ, rfl⟩
def spineStep (v : Vertex) : Vertex :=
  if v.up then down v.col v.row else up (v.col + 1) v.row
def spine (o : Vertex) (k : ℕ) : Vertex :=
  spineStep^[k] o
def spineRank (v : Vertex) : ℤ :=
  2 * v.col + if v.up then 0 else 1
lemma spineStep_rank (v : Vertex) :
    spineRank (spineStep v) = spineRank v + 1 := by
  rcases v with ⟨c, r, u⟩
  cases u
  · simp [spineStep, spineRank, up]
    omega
  · simp [spineStep, spineRank, down]
lemma spineStep_mem_neighbors (v : Vertex) :
    spineStep v ∈ neighbors v := by
  rcases v with ⟨c, r, u⟩
  cases u <;> simp [spineStep, neighbors, up, down]
lemma spine_succ (o : Vertex) (k : ℕ) :
    spine o (k + 1) = spineStep (spine o k) := by
  simp [spine, Function.iterate_succ_apply']
lemma spineRank_spine (o : Vertex) (k : ℕ) :
    spineRank (spine o k) = spineRank o + (k : ℤ) := by
  induction k with
  | zero => simp [spine]
  | succ k ih =>
      rw [spine_succ, spineStep_rank, ih]
      push_cast
      omega
lemma spine_nat_injective (o : Vertex) : Function.Injective (spine o) := by
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hrank : spineRank (spine o i) < spineRank (spine o j) := by
      rw [spineRank_spine, spineRank_spine]
      omega
    rw [hij] at hrank
    exact (lt_irrefl _ hrank)
  · have hrank : spineRank (spine o j) < spineRank (spine o i) := by
      rw [spineRank_spine, spineRank_spine]
      omega
    rw [hij] at hrank
    exact (lt_irrefl _ hrank)
def saws (o : Vertex) (n : ℕ) : Finset (List Vertex) :=
  (walkLists o n).filter List.Nodup

lemma exists_mem_saws (o : Vertex) (n : ℕ) :
    ∃ γ : List Vertex, γ ∈ saws o n := by
  let f : Fin (n + 1) → Vertex := fun k => spine o (k : ℕ)
  let γ : List Vertex := List.ofFn f
  refine ⟨γ, ?_⟩
  rw [saws, Finset.mem_filter]
  constructor
  · rw [mem_walkLists_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp [γ, f, List.ofFn_succ, spine]
    · simp [γ, f]
    · rw [List.isChain_ofFn]
      intro i hi
      change spine o ((i + 1 : ℕ)) ∈ neighbors (spine o i)
      rw [spine_succ]
      exact spineStep_mem_neighbors _
  · exact List.nodup_ofFn_ofInjective (fun i j hij => Fin.ext (spine_nat_injective o hij))
def endpoint (o : Vertex) (γ : List Vertex) : Vertex := γ.getLastD o

def displacement (o : Vertex) (γ : List Vertex) : ℂ :=
  position (endpoint o γ) - position o

def projection (e z : ℂ) : ℝ := (star e * z).re

def partition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  ∑ γ ∈ saws o n, rho ^ n * Real.exp (s * projection e (displacement o γ))

lemma partition_nonneg (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 ≤ partition o e s n := by
  unfold partition
  refine Finset.sum_nonneg ?_
  intro γ hγ
  exact mul_nonneg (pow_nonneg (by unfold rho; positivity) n)
    (le_of_lt (Real.exp_pos _))
lemma partition_pos (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    0 < partition o e s n := by
  obtain ⟨γ, hγ⟩ := exists_mem_saws o n
  unfold partition
  refine Finset.sum_pos' ?_ ⟨γ, hγ, ?_⟩
  · intro δ hδ
    exact mul_nonneg (pow_nonneg (by unfold rho; positivity) n)
      (le_of_lt (Real.exp_pos _))
  · exact mul_pos (pow_pos (by unfold rho; positivity) n) (Real.exp_pos _)
def pT_vtrans (k l : ℤ) (v : Vertex) : Vertex := ⟨v.col + k, v.row + l, v.up⟩
lemma pT_up (k l c r : ℤ) :
    pT_vtrans k l (up c r) = up (c + k) (r + l) := rfl
lemma pT_down (k l c r : ℤ) :
    pT_vtrans k l (down c r) = down (c + k) (r + l) := rfl
lemma pT_up_mk_eq (c r c' r' : ℤ) : (up c r = up c' r') ↔ c = c' ∧ r = r' := by
  constructor
  · intro h; exact ⟨congrArg Vertex.col h, congrArg Vertex.row h⟩
  · rintro ⟨rfl, rfl⟩; rfl
lemma pT_down_mk_eq (c r c' r' : ℤ) : (down c r = down c' r') ↔ c = c' ∧ r = r' := by
  constructor
  · intro h; exact ⟨congrArg Vertex.col h, congrArg Vertex.row h⟩
  · rintro ⟨rfl, rfl⟩; rfl
lemma pT_inv (k l : ℤ) (v : Vertex) : pT_vtrans (-k) (-l) (pT_vtrans k l v) = v := by
  rcases v with ⟨c, r, u⟩
  simp only [pT_vtrans, Vertex.mk.injEq, and_true]
  exact ⟨by omega, by omega⟩
lemma pT_inv' (k l : ℤ) (v : Vertex) : pT_vtrans k l (pT_vtrans (-k) (-l) v) = v := by
  rcases v with ⟨c, r, u⟩
  simp only [pT_vtrans, Vertex.mk.injEq, and_true]
  exact ⟨by omega, by omega⟩
lemma pT_injective (k l : ℤ) : Function.Injective (pT_vtrans k l) := by
  rintro ⟨c, r, u⟩ ⟨c', r', u'⟩ h
  simp only [pT_vtrans, Vertex.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have h1' : c = c' := by omega
  have h2' : r = r' := by omega
  subst h1'; subst h2'; subst h3
  rfl
lemma pT_map_comp (k l : ℤ) (γ : List Vertex) :
    (γ.map (pT_vtrans k l)).map (pT_vtrans (-k) (-l)) = γ := by
  induction γ with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨pT_inv k l a, ih⟩
lemma pT_map_comp' (k l : ℤ) (γ : List Vertex) :
    (γ.map (pT_vtrans (-k) (-l))).map (pT_vtrans k l) = γ := by
  induction γ with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨pT_inv' k l a, ih⟩
lemma pT_map_injective (k l : ℤ) :
    Function.Injective (fun γ : List Vertex => γ.map (pT_vtrans k l)) := by
  intro a b h
  have h' := congrArg (fun γ : List Vertex => γ.map (pT_vtrans (-k) (-l))) h
  rwa [pT_map_comp, pT_map_comp] at h'
lemma pT_mem_neighbors_up (c r : ℤ) (w : Vertex) :
    w ∈ neighbors (up c r) ↔ w = down c (r - 1) ∨ w = down c r ∨ w = down (c - 1) r := by
  simp only [neighbors, up, ite_true, Finset.mem_insert, Finset.mem_singleton]
lemma pT_mem_neighbors_down (c r : ℤ) (w : Vertex) :
    w ∈ neighbors (down c r) ↔ w = up c (r + 1) ∨ w = up c r ∨ w = up (c + 1) r := by
  simp only [neighbors, down, Bool.false_eq_true, ite_false, Finset.mem_insert,
    Finset.mem_singleton]
lemma pT_down_not_mem_neighbors (c r c' r' : ℤ) :
    down c' r' ∉ neighbors (down c r) := by
  rw [pT_mem_neighbors_down]
  rintro (h | h | h) <;> exact Bool.noConfusion (congrArg Vertex.up h)
lemma pT_up_not_mem_neighbors (c r c' r' : ℤ) :
    up c' r' ∉ neighbors (up c r) := by
  rw [pT_mem_neighbors_up]
  rintro (h | h | h) <;> exact Bool.noConfusion (congrArg Vertex.up h)
lemma pT_mem_neighbors_iff (k l : ℤ) (a b : Vertex) :
    pT_vtrans k l b ∈ neighbors (pT_vtrans k l a) ↔ b ∈ neighbors a := by
  rcases a with ⟨c, r, u⟩
  rcases b with ⟨c', r', u'⟩
  cases u with
  | false =>
      cases u' with
      | false =>
          rw [show (⟨c, r, false⟩ : Vertex) = down c r from rfl,
            show (⟨c', r', false⟩ : Vertex) = down c' r' from rfl,
            pT_down, pT_down]
          exact ⟨fun h => absurd h (pT_down_not_mem_neighbors (c + k) (r + l) (c' + k) (r' + l)),
            fun h => absurd h (pT_down_not_mem_neighbors c r c' r')⟩
      | true =>
          rw [show (⟨c, r, false⟩ : Vertex) = down c r from rfl,
            show (⟨c', r', true⟩ : Vertex) = up c' r' from rfl,
            pT_down, pT_up, pT_mem_neighbors_down, pT_mem_neighbors_down]
          simp only [pT_up_mk_eq]
          omega
  | true =>
      cases u' with
      | false =>
          rw [show (⟨c, r, true⟩ : Vertex) = up c r from rfl,
            show (⟨c', r', false⟩ : Vertex) = down c' r' from rfl,
            pT_up, pT_down, pT_mem_neighbors_up, pT_mem_neighbors_up]
          simp only [pT_down_mk_eq]
          omega
      | true =>
          rw [show (⟨c, r, true⟩ : Vertex) = up c r from rfl,
            show (⟨c', r', true⟩ : Vertex) = up c' r' from rfl,
            pT_up, pT_up]
          exact ⟨fun h => absurd h (pT_up_not_mem_neighbors (c + k) (r + l) (c' + k) (r' + l)),
            fun h => absurd h (pT_up_not_mem_neighbors c r c' r')⟩
lemma pT_isChain_map_iff (k l : ℤ) (γ : List Vertex) :
    List.IsChain (fun a b : Vertex => b ∈ neighbors a) (γ.map (pT_vtrans k l)) ↔
      List.IsChain (fun a b : Vertex => b ∈ neighbors a) γ := by
  rw [List.isChain_map]
  exact List.IsChain.iff (fun a b => pT_mem_neighbors_iff k l a b)
lemma pT_mem_walkLists_map (k l : ℤ) {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ ∈ walkLists o n) : γ.map (pT_vtrans k l) ∈ walkLists (pT_vtrans k l o) n := by
  rw [mem_walkLists_iff] at h ⊢
  obtain ⟨hhead, hlen, hchain⟩ := h
  refine ⟨?_, by simp [hlen], (pT_isChain_map_iff k l γ).mpr hchain⟩
  rw [List.head?_map, hhead]
  rfl
lemma pT_mem_walkLists_of_map (k l : ℤ) {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ.map (pT_vtrans k l) ∈ walkLists (pT_vtrans k l o) n) : γ ∈ walkLists o n := by
  have h' := pT_mem_walkLists_map (-k) (-l) h
  rw [pT_inv] at h'
  rwa [pT_map_comp] at h'
lemma pT_mem_saws_map (k l : ℤ) {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ ∈ saws o n) : γ.map (pT_vtrans k l) ∈ saws (pT_vtrans k l o) n := by
  rw [saws, Finset.mem_filter] at h ⊢
  exact ⟨pT_mem_walkLists_map k l h.1, h.2.map (pT_injective k l)⟩
lemma pT_mem_saws_of_map (k l : ℤ) {o : Vertex} {n : ℕ} {γ : List Vertex}
    (h : γ.map (pT_vtrans k l) ∈ saws (pT_vtrans k l o) n) : γ ∈ saws o n := by
  have h' := pT_mem_saws_map (-k) (-l) h
  rw [pT_inv] at h'
  rwa [pT_map_comp] at h'
lemma pT_saws (k l : ℤ) (o : Vertex) (n : ℕ) :
    saws (pT_vtrans k l o) n = (saws o n).image (fun γ : List Vertex => γ.map (pT_vtrans k l)) := by
  ext γ
  rw [Finset.mem_image]
  constructor
  · intro hγ
    have hγ' : (γ.map (pT_vtrans (-k) (-l))).map (pT_vtrans k l) ∈ saws (pT_vtrans k l o) n := by
      rw [pT_map_comp']
      exact hγ
    exact ⟨γ.map (pT_vtrans (-k) (-l)), pT_mem_saws_of_map k l hγ', pT_map_comp' k l γ⟩
  · rintro ⟨δ, hδ, rfl⟩
    exact pT_mem_saws_map k l hδ
lemma pT_position_sub (k l : ℤ) (v w : Vertex) :
    position (pT_vtrans k l v) - position (pT_vtrans k l w) = position v - position w := by
  rcases v with ⟨c, r, u⟩
  rcases w with ⟨c', r', u'⟩
  cases u <;> cases u' <;>
    · apply Complex.ext <;>
        simp only [pT_vtrans, position, Bool.false_eq_true, ite_false, ite_true, Complex.sub_re,
          Complex.sub_im] <;>
        push_cast <;> ring
lemma pT_displacement_map (k l : ℤ) (o : Vertex) (γ : List Vertex) :
    displacement (pT_vtrans k l o) (γ.map (pT_vtrans k l)) = displacement o γ := by
  unfold displacement endpoint
  rw [List.getLastD_map]
  exact pT_position_sub k l _ o
lemma pT_partition (k l : ℤ) (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition (pT_vtrans k l o) e s n = partition o e s n := by
  unfold partition
  rw [pT_saws k l o n,
    Finset.sum_image (g := fun γ : List Vertex => γ.map (pT_vtrans k l))]
  · refine Finset.sum_congr rfl ?_
    intro γ hγ
    rw [pT_displacement_map]
  · intro a _ b _ hab
    exact pT_map_injective k l hab
lemma partition_eq_of_up_eq {o o' : Vertex} (h : o.up = o'.up) (e : ℂ) (s : ℝ) (n : ℕ) :
    partition o e s n = partition o' e s n := by
  have ho : o' = pT_vtrans (o'.col - o.col) (o'.row - o.row) o := by
    rcases o with ⟨c, r, u⟩
    rcases o' with ⟨c', r', u'⟩
    simp only [pT_vtrans, Vertex.mk.injEq]
    exact ⟨by omega, by omega, h.symm⟩
  rw [ho]
  exact (pT_partition (o'.col - o.col) (o'.row - o.row) o e s n).symm
def spineWalk (o : Vertex) (n : ℕ) : List Vertex :=
  List.ofFn (fun k : Fin (n + 1) => spine o k)
lemma spineWalk_mem_saws (o : Vertex) (n : ℕ) : spineWalk o n ∈ saws o n := by
  unfold spineWalk
  rw [saws, Finset.mem_filter]
  constructor
  · rw [mem_walkLists_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp [List.ofFn_succ, spine]
    · simp
    · rw [List.isChain_ofFn]
      intro i hi
      change spine o ((i + 1 : ℕ)) ∈ neighbors (spine o i)
      rw [spine_succ]
      exact spineStep_mem_neighbors _
  · exact List.nodup_ofFn_ofInjective (fun i j hij => Fin.ext (spine_nat_injective o hij))
lemma endpoint_spineWalk (o : Vertex) (n : ℕ) :
    endpoint o (spineWalk o n) = spine o n := by
  unfold endpoint spineWalk
  rw [List.getLastD_eq_getLast?]
  have hne : List.ofFn (fun k : Fin (n + 1) => spine o k) ≠ [] := by simp
  rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn_succ]
  congr
lemma spine_up (j : ℕ) : spine (up 0 0) (2 * j) = up (j : ℤ) 0 := by
  induction j with
  | zero => simp [spine]
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, spine_succ, spine_succ, ih]
      simp [spineStep, up, down]
lemma position_spine_even (j : ℕ) :
    position (spine (up 0 0) (2 * j)) = ⟨(j : ℝ) + 1 / 2, rowSpacing / 3⟩ := by
  rw [spine_up]
  simp [position, up, div_eq_mul_inv]
lemma position_up_origin :
    position (up 0 0) = ⟨1 / 2, rowSpacing / 3⟩ := by
  simp [position, up, div_eq_mul_inv]
lemma displacement_spine_even (p : ℕ) :
    displacement (up 0 0) (spineWalk (up 0 0) (2 * p)) = (p : ℂ) := by
  unfold displacement
  rw [endpoint_spineWalk, position_spine_even, position_up_origin]
  apply Complex.ext <;> simp
lemma projection_ofReal (e : ℂ) (r : ℝ) :
    projection e (r : ℂ) = r * e.re := by
  unfold projection
  rw [Complex.mul_re]
  simp
  ring
lemma partition_up_even_ge (e : ℂ) (s : ℝ) (p : ℕ) :
    rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      partition (up 0 0) e s (2 * p) := by
  let γ := spineWalk (up 0 0) (2 * p)
  have hγ : γ ∈ saws (up 0 0) (2 * p) := spineWalk_mem_saws _ _
  have hnonneg : ∀ δ ∈ saws (up 0 0) (2 * p),
      0 ≤ rho ^ (2 * p) * Real.exp (s * projection e (displacement (up 0 0) δ)) := by
    intro δ hδ
    exact mul_nonneg (pow_nonneg (by unfold rho; positivity) _) (le_of_lt (Real.exp_pos _))
  have hsingle := Finset.single_le_sum hnonneg hγ
  have hproj : projection e (displacement (up 0 0) γ) = (p : ℝ) * e.re := by
    rw [show displacement (up 0 0) γ = (p : ℂ) by simp [γ, displacement_spine_even]]
    exact projection_ofReal e (p : ℝ)
  have hexp : Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      Real.exp (s * projection e (displacement (up 0 0) γ)) := by
    apply Real.exp_le_exp.mpr
    rw [hproj]
    have h1 : -( |s| * (p : ℝ) * |e.re| ) ≤ s * ((p : ℝ) * e.re) := by
      have h2 : -|s * ((p : ℝ) * e.re)| ≤ s * ((p : ℝ) * e.re) := neg_abs_le _
      have h3 : |s * ((p : ℝ) * e.re)| = |s| * (p : ℝ) * |e.re| := by
        calc
          |s * ((p : ℝ) * e.re)| = |s| * |(p : ℝ) * e.re| := by rw [abs_mul]
          _ = |s| * (|(p : ℝ)| * |e.re|) := by rw [abs_mul]
          _ = |s| * ((p : ℝ) * |e.re|) := by
            rw [abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
          _ = |s| * (p : ℝ) * |e.re| := by ring
      linarith
    exact h1
  have hsummand : rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      rho ^ (2 * p) * Real.exp (s * projection e (displacement (up 0 0) γ)) := by
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg (by unfold rho; positivity) _)
  calc
    rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))
        ≤ rho ^ (2 * p) * Real.exp (s * projection e (displacement (up 0 0) γ)) := hsummand
    _ ≤ partition (up 0 0) e s (2 * p) := by
      simpa [partition, γ] using hsingle
lemma even_log_bddBelow_up (e : ℂ) (s : ℝ) :
    BddBelow (Set.range (fun p : ℕ =>
      Real.log (partition (up 0 0) e s (2 * p)) / (p : ℝ))) := by
  let L : ℝ := 2 * Real.log rho - |s| * |e.re|
  refine ⟨min 0 L, ?_⟩
  rintro y ⟨p, rfl⟩
  by_cases hp : p = 0
  · subst p
    simpa using (min_le_left (0 : ℝ) L)
  · have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
    have hlowpos : 0 < rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) := by
      exact mul_pos (pow_pos (by unfold rho; positivity) _) (Real.exp_pos _)
    have hlog : Real.log (rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))) ≤
        Real.log (partition (up 0 0) e s (2 * p)) := by
      exact Real.log_le_log hlowpos (partition_up_even_ge e s p)
    have hcalc : Real.log (rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))) / (p : ℝ) = L := by
      rw [Real.log_mul (ne_of_gt (pow_pos (by unfold rho; positivity) _))
        (ne_of_gt (Real.exp_pos _)), Real.log_pow, Real.log_exp]
      unfold L
      field_simp [hpR.ne']
      norm_num [Nat.cast_mul]
      ring
    have hquot : L ≤ Real.log (partition (up 0 0) e s (2 * p)) / (p : ℝ) := by
      rw [← hcalc]
      exact div_le_div_of_nonneg_right hlog (le_of_lt hpR)
    exact le_trans (min_le_right _ _) hquot
lemma dy_endpoint_ofFn_spine (o : Vertex) (n : ℕ) :
    endpoint o (List.ofFn (fun k : Fin (n + 1) => spine o k)) = spine o n := by
  unfold endpoint
  rw [List.getLastD_eq_getLast?]
  have hne : List.ofFn (fun k : Fin (n + 1) => spine o k) ≠ [] := by simp
  rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn_succ]
  congr
lemma dy_ofFn_spine_mem_saws (o : Vertex) (n : ℕ) :
    List.ofFn (fun k : Fin (n + 1) => spine o k) ∈ saws o n := by
  rw [saws, Finset.mem_filter]
  constructor
  · rw [mem_walkLists_iff]
    refine ⟨?_, ?_, ?_⟩
    · simp [List.ofFn_succ, spine]
    · simp
    · rw [List.isChain_ofFn]
      intro i hi
      change spine o ((i + 1 : ℕ)) ∈ neighbors (spine o i)
      rw [spine_succ]
      exact spineStep_mem_neighbors _
  · exact List.nodup_ofFn_ofInjective (fun i j hij => Fin.ext (spine_nat_injective o hij))
lemma dy_spine_down (j : ℕ) : spine (down 0 0) (2 * j) = down (j : ℤ) 0 := by
  induction j with
  | zero => simp [spine]
  | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega, spine_succ, spine_succ, ih]
      simp [spineStep, up, down]
lemma dy_position_spine_down (j : ℕ) :
    position (spine (down 0 0) (2 * j)) = ⟨(j : ℝ) + 1, 2 * rowSpacing / 3⟩ := by
  rw [dy_spine_down]
  apply Complex.ext <;> simp [position, down, div_eq_mul_inv] <;> ring
lemma dy_position_down_origin :
    position (down 0 0) = ⟨1, 2 * rowSpacing / 3⟩ := by
  apply Complex.ext <;> simp [position, down, div_eq_mul_inv] <;> ring
lemma dy_displacement_spine_down (p : ℕ) :
    displacement (down 0 0)
      (List.ofFn (fun k : Fin (2 * p + 1) => spine (down 0 0) k)) = (p : ℂ) := by
  unfold displacement
  rw [dy_endpoint_ofFn_spine, dy_position_spine_down, dy_position_down_origin]
  apply Complex.ext <;> simp
lemma dy_projection_ofReal (e : ℂ) (r : ℝ) :
    projection e (r : ℂ) = r * e.re := by
  unfold projection
  rw [Complex.mul_re]
  simp
  ring
lemma partition_down_even_ge (e : ℂ) (s : ℝ) (p : ℕ) :
    rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      partition (down 0 0) e s (2 * p) := by
  let γ := List.ofFn (fun k : Fin (2 * p + 1) => spine (down 0 0) k)
  have hγ : γ ∈ saws (down 0 0) (2 * p) := dy_ofFn_spine_mem_saws _ _
  have hnonneg : ∀ δ ∈ saws (down 0 0) (2 * p),
      0 ≤ rho ^ (2 * p) * Real.exp (s * projection e (displacement (down 0 0) δ)) := by
    intro δ hδ
    exact mul_nonneg (pow_nonneg (by unfold rho; positivity) _) (le_of_lt (Real.exp_pos _))
  have hsingle := Finset.single_le_sum hnonneg hγ
  have hproj : projection e (displacement (down 0 0) γ) = (p : ℝ) * e.re := by
    rw [show displacement (down 0 0) γ = (p : ℂ) from by
      simpa [γ] using dy_displacement_spine_down p]
    exact dy_projection_ofReal e (p : ℝ)
  have hexp : Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      Real.exp (s * projection e (displacement (down 0 0) γ)) := by
    apply Real.exp_le_exp.mpr
    rw [hproj]
    have h1 : -( |s| * (p : ℝ) * |e.re| ) ≤ s * ((p : ℝ) * e.re) := by
      have h2 : -|s * ((p : ℝ) * e.re)| ≤ s * ((p : ℝ) * e.re) := neg_abs_le _
      have h3 : |s * ((p : ℝ) * e.re)| = |s| * (p : ℝ) * |e.re| := by
        calc
          |s * ((p : ℝ) * e.re)| = |s| * |(p : ℝ) * e.re| := by rw [abs_mul]
          _ = |s| * (|(p : ℝ)| * |e.re|) := by rw [abs_mul]
          _ = |s| * ((p : ℝ) * |e.re|) := by
            rw [abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
          _ = |s| * (p : ℝ) * |e.re| := by ring
      linarith
    exact h1
  have hsummand : rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) ≤
      rho ^ (2 * p) * Real.exp (s * projection e (displacement (down 0 0) γ)) := by
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg (by unfold rho; positivity) _)
  calc
    rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))
        ≤ rho ^ (2 * p) * Real.exp (s * projection e (displacement (down 0 0) γ)) := hsummand
    _ ≤ partition (down 0 0) e s (2 * p) := by
      simpa [partition, γ] using hsingle
lemma even_log_bddBelow_down (e : ℂ) (s : ℝ) :
    BddBelow (Set.range (fun p : ℕ =>
      Real.log (partition (down 0 0) e s (2 * p)) / (p : ℝ))) := by
  let L : ℝ := 2 * Real.log rho - |s| * |e.re|
  refine ⟨min 0 L, ?_⟩
  rintro y ⟨p, rfl⟩
  by_cases hp : p = 0
  · subst p
    simpa using (min_le_left (0 : ℝ) L)
  · have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
    have hlowpos : 0 < rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|)) := by
      exact mul_pos (pow_pos (by unfold rho; positivity) _) (Real.exp_pos _)
    have hlog : Real.log (rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))) ≤
        Real.log (partition (down 0 0) e s (2 * p)) := by
      exact Real.log_le_log hlowpos (partition_down_even_ge e s p)
    have hcalc : Real.log (rho ^ (2 * p) * Real.exp (-(|s| * (p : ℝ) * |e.re|))) / (p : ℝ) = L := by
      rw [Real.log_mul (ne_of_gt (pow_pos (by unfold rho; positivity) _))
        (ne_of_gt (Real.exp_pos _)), Real.log_pow, Real.log_exp]
      unfold L
      field_simp [hpR.ne']
      norm_num [Nat.cast_mul]
      ring
    have hquot : L ≤ Real.log (partition (down 0 0) e s (2 * p)) / (p : ℝ) := by
      rw [← hcalc]
      exact div_le_div_of_nonneg_right hlog (le_of_lt hpR)
    exact le_trans (min_le_right _ _) hquot
lemma splitP_projection_add (e z w : ℂ) :
    projection e (z + w) = projection e z + projection e w := by
  simp [projection, mul_add]
lemma splitP_weight (e : ℂ) (s : ℝ) (m n : ℕ) (z w : ℂ) :
    rho ^ (m + n) * Real.exp (s * projection e (z + w)) =
      (rho ^ m * Real.exp (s * projection e z)) *
        (rho ^ n * Real.exp (s * projection e w)) := by
  rw [splitP_projection_add, mul_add, Real.exp_add, pow_add]
  ring
lemma splitP_getLastD_drop {α : Type*} (l : List α) (i : ℕ) (h : i < l.length) (a b : α) :
    (l.drop i).getLastD a = l.getLastD b := by
  have hl : l ≠ [] := by intro h0; subst l; simp at h
  rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_drop,
    if_neg (by omega : ¬ l.length ≤ i)]
  cases hlast : l.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hlast; exact absurd hlast hl
  | some x => simp
lemma splitP_getLastD_take_succ {α : Type*} (l : List α) (i : ℕ) (h : i < l.length) (a : α) :
    (l.take (i + 1)).getLastD a = l[i] := by
  rw [List.getLastD_eq_getLast?, List.getLast?_take, if_neg (by omega)]
  have hi : i + 1 - 1 = i := by omega
  rw [hi, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
  simp
lemma splitP_take_append_drop_tail {α : Type*} (γ : List α) (m : ℕ) :
    γ.take (m + 1) ++ (γ.drop m).tail = γ := by
  rcases lt_or_ge m γ.length with h | h
  · have htake : γ.take (m + 1) = γ.take m ++ [γ[m]] := by
      rw [List.take_add_one, List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩]
      simp
    rw [htake, List.append_assoc]
    have hcons : [γ[m]] ++ (γ.drop m).tail = γ.drop m := by
      rw [List.drop_eq_getElem_cons h]
      simp
    rw [hcons, List.take_append_drop]
  · have htake : γ.take (m + 1) = γ := List.take_of_length_le (by omega)
    have hdrop : γ.drop m = [] := List.drop_eq_nil_iff.mpr h
    rw [htake, hdrop]
    simp
lemma splitP_take_drop_injective {α : Type*} (m : ℕ) :
    Function.Injective (fun γ : List α => (γ.take (m + 1), γ.drop m)) := by
  rintro γ₁ γ₂ h
  have h1 : γ₁.take (m + 1) = γ₂.take (m + 1) := congrArg Prod.fst h
  have h2 : γ₁.drop m = γ₂.drop m := congrArg Prod.snd h
  rw [← splitP_take_append_drop_tail γ₁ m, ← splitP_take_append_drop_tail γ₂ m, h1, h2]
lemma splitP_take_mem_saws {o : Vertex} {m n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (m + n)) :
    γ.take (m + 1) ∈ saws o m := by
  classical
  rw [saws, Finset.mem_filter] at hγ ⊢
  obtain ⟨hwalk, hnd⟩ := hγ
  obtain ⟨hhead, hlen, hchain⟩ := mem_walkLists_iff.mp hwalk
  refine ⟨mem_walkLists_iff.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.head?_take, if_neg (by omega)]
    exact hhead
  · rw [List.length_take]
    omega
  · exact hchain.take (m + 1)
  · exact List.Nodup.sublist (List.take_sublist (m + 1) γ) hnd
lemma splitP_drop_mem_saws {o : Vertex} {m n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (m + n)) :
    γ.drop m ∈ saws (endpoint o (γ.take (m + 1))) n := by
  classical
  rw [saws, Finset.mem_filter] at hγ ⊢
  obtain ⟨hwalk, hnd⟩ := hγ
  obtain ⟨hhead, hlen, hchain⟩ := mem_walkLists_iff.mp hwalk
  have hm : m < γ.length := by omega
  have hend : endpoint o (γ.take (m + 1)) = γ[m] :=
    splitP_getLastD_take_succ γ m hm o
  refine ⟨mem_walkLists_iff.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.head?_drop, List.getElem?_eq_some_iff.mpr ⟨hm, rfl⟩, hend]
  · rw [List.length_drop]
    omega
  · exact hchain.drop m
  · exact List.Nodup.sublist (List.drop_sublist m γ) hnd
lemma splitP_endpoint_drop {o : Vertex} {m n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (m + n)) :
    endpoint (endpoint o (γ.take (m + 1))) (γ.drop m) = endpoint o γ := by
  classical
  rw [saws, Finset.mem_filter, mem_walkLists_iff] at hγ
  obtain ⟨⟨_, hlen, _⟩, _⟩ := hγ
  have hm : m < γ.length := by omega
  unfold endpoint
  exact splitP_getLastD_drop γ m hm _ o
lemma splitP_displacement {o : Vertex} {m n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ saws o (m + n)) :
    displacement o γ =
      displacement o (γ.take (m + 1)) +
        displacement (endpoint o (γ.take (m + 1))) (γ.drop m) := by
  unfold displacement
  rw [splitP_endpoint_drop hγ]
  ring
theorem partition_split_le (o : Vertex) (e : ℂ) (s : ℝ) (m n : ℕ) :
    partition o e s (m + n) ≤
      partition o e s m *
        max (partition (up 0 0) e s n) (partition (down 0 0) e s n) := by
  classical
  set M := max (partition (up 0 0) e s n) (partition (down 0 0) e s n) with hM
  have hrho : 0 ≤ rho := by unfold rho; positivity
  let f : List Vertex → Sigma (fun _ : List Vertex => List Vertex) :=
    fun γ => ⟨γ.take (m + 1), γ.drop m⟩
  let V : Sigma (fun _ : List Vertex => List Vertex) → ℝ := fun x =>
    (rho ^ m * Real.exp (s * projection e (displacement o x.1))) *
      (rho ^ n * Real.exp (s * projection e (displacement (endpoint o x.1) x.2)))
  let W : List Vertex → ℝ := fun γ =>
    rho ^ (m + n) * Real.exp (s * projection e (displacement o γ))
  have hW : ∀ γ ∈ saws o (m + n), W γ = V (f γ) := by
    intro γ hγ
    simp only [W, V, f]
    rw [splitP_displacement hγ]
    exact splitP_weight e s m n _ _
  have hf_inj : Function.Injective f := by
    rintro γ₁ γ₂ h
    have h1 : γ₁.take (m + 1) = γ₂.take (m + 1) := congrArg Sigma.fst h
    have h2 : γ₁.drop m = γ₂.drop m := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [← splitP_take_append_drop_tail γ₁ m, ← splitP_take_append_drop_tail γ₂ m, h1, h2]
  have hsubset : (saws o (m + n)).image f ⊆
      (saws o m).sigma (fun α => saws (endpoint o α) n) := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sigma.mpr ⟨splitP_take_mem_saws hγ, splitP_drop_mem_saws hγ⟩
  have hVnonneg : ∀ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), 0 ≤ V x := by
    rintro ⟨α, β⟩ hx
    simp only [V]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hrho m) (Real.exp_pos _).le)
      (mul_nonneg (pow_nonneg hrho n) (Real.exp_pos _).le)
  have hpartition_le_M : ∀ α : List Vertex,
      partition (endpoint o α) e s n ≤ M := by
    intro α
    cases hup : (endpoint o α).up
    · have h := partition_eq_of_up_eq (o := endpoint o α) (o' := down 0 0)
        (by simpa [down] using hup) e s n
      rw [h, hM]
      exact le_max_right _ _
    · have h := partition_eq_of_up_eq (o := endpoint o α) (o' := up 0 0)
        (by simpa [up] using hup) e s n
      rw [h, hM]
      exact le_max_left _ _
  calc partition o e s (m + n)
      = ∑ γ ∈ saws o (m + n), W γ := rfl
    _ = ∑ γ ∈ saws o (m + n), V (f γ) := Finset.sum_congr rfl hW
    _ = ∑ x ∈ (saws o (m + n)).image f, V x := (Finset.sum_image hf_inj.injOn).symm
    _ ≤ ∑ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), V x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun x hx _ => hVnonneg x hx)
    _ = ∑ α ∈ saws o m, ∑ β ∈ saws (endpoint o α) n, V ⟨α, β⟩ :=
        Finset.sum_sigma _ _ _
    _ = ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) *
            partition (endpoint o α) e s n := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [partition, Finset.mul_sum]
    _ ≤ ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) * M := by
        apply Finset.sum_le_sum
        intro α hα
        exact mul_le_mul_of_nonneg_left (hpartition_le_M α)
          (mul_nonneg (pow_nonneg hrho m) (Real.exp_pos _).le)
    _ = (∑ α ∈ saws o m,
          rho ^ m * Real.exp (s * projection e (displacement o α))) * M :=
        (Finset.sum_mul _ _ _).symm
    _ = partition o e s m * M := rfl
lemma up_flip_of_mem_neighbors {v w : Vertex} (h : w ∈ neighbors v) : w.up = !v.up := by
  rcases v with ⟨c, r, u⟩
  rcases w with ⟨c', r', u'⟩
  cases u <;> cases u' <;> simp [neighbors, up, down] at h ⊢
lemma endpoint_up_parity {o : Vertex} {n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ walkLists o n) :
    (endpoint o γ).up = if n % 2 = 0 then o.up else !o.up := by
  induction n generalizing o γ with
  | zero =>
      rw [mem_walkLists_iff] at hγ
      obtain ⟨hhead, hlen, -⟩ := hγ
      have hγ' : γ = [o] := by
        cases γ with
        | nil => simp at hhead
        | cons a t =>
            have hao : a = o := by simpa using hhead
            have ht : t = [] := by
              have h0 : t.length = 0 := by simpa using hlen
              simpa using h0
            rw [ht, hao]
      rw [hγ']
      simp [endpoint]
  | succ n ih =>
      rw [mem_walkLists_iff] at hγ
      obtain ⟨hhead, hlen, hchain⟩ := hγ
      cases γ with
      | nil => simp at hhead
      | cons a t =>
          have hao : a = o := by simpa using hhead
          cases t with
          | nil => simp at hlen
          | cons v t' =>
              rw [List.isChain_cons] at hchain
              obtain ⟨hrel, hchain'⟩ := hchain
              have hv : v ∈ neighbors a := hrel v (by simp)
              have htlen : (v :: t').length = n + 1 := by simpa using hlen
              have hδ : (v :: t') ∈ walkLists v n := by
                rw [mem_walkLists_iff]
                exact ⟨rfl, htlen, hchain'⟩
              have hend : endpoint o (a :: v :: t') = endpoint v (v :: t') := by
                unfold endpoint
                rw [List.getLastD_cons, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
                  List.getLast?_cons]
                rfl
              rw [hend, ih hδ, up_flip_of_mem_neighbors hv, hao]
              by_cases hn : n % 2 = 0
              · have h1 : (n + 1) % 2 = 1 := by omega
                simp [hn, h1]
              · have h1 : (n + 1) % 2 = 0 := by omega
                simp [hn, h1]
lemma partition_split_le_same {o : Vertex} (e : ℂ) (s : ℝ) (m n : ℕ)
    (hup : ∀ α ∈ saws o m, (endpoint o α).up = o.up) :
    partition o e s (m + n) ≤ partition o e s m * partition o e s n := by
  classical
  have hrho : 0 ≤ rho := by unfold rho; positivity
  let f : List Vertex → Sigma (fun _ : List Vertex => List Vertex) :=
    fun γ => ⟨γ.take (m + 1), γ.drop m⟩
  let V : Sigma (fun _ : List Vertex => List Vertex) → ℝ := fun x =>
    (rho ^ m * Real.exp (s * projection e (displacement o x.1))) *
      (rho ^ n * Real.exp (s * projection e (displacement (endpoint o x.1) x.2)))
  let W : List Vertex → ℝ := fun γ =>
    rho ^ (m + n) * Real.exp (s * projection e (displacement o γ))
  have hW : ∀ γ ∈ saws o (m + n), W γ = V (f γ) := by
    intro γ hγ
    simp only [W, V, f]
    rw [splitP_displacement hγ]
    exact splitP_weight e s m n _ _
  have hf_inj : Function.Injective f := by
    rintro γ₁ γ₂ h
    have h1 : γ₁.take (m + 1) = γ₂.take (m + 1) := congrArg Sigma.fst h
    have h2 : γ₁.drop m = γ₂.drop m := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [← splitP_take_append_drop_tail γ₁ m, ← splitP_take_append_drop_tail γ₂ m, h1, h2]
  have hsubset : (saws o (m + n)).image f ⊆
      (saws o m).sigma (fun α => saws (endpoint o α) n) := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sigma.mpr ⟨splitP_take_mem_saws hγ, splitP_drop_mem_saws hγ⟩
  have hVnonneg : ∀ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), 0 ≤ V x := by
    rintro ⟨α, β⟩ hx
    simp only [V]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hrho m) (Real.exp_pos _).le)
      (mul_nonneg (pow_nonneg hrho n) (Real.exp_pos _).le)
  calc partition o e s (m + n)
      = ∑ γ ∈ saws o (m + n), W γ := rfl
    _ = ∑ γ ∈ saws o (m + n), V (f γ) := Finset.sum_congr rfl hW
    _ = ∑ x ∈ (saws o (m + n)).image f, V x := (Finset.sum_image hf_inj.injOn).symm
    _ ≤ ∑ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), V x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun x hx _ => hVnonneg x hx)
    _ = ∑ α ∈ saws o m, ∑ β ∈ saws (endpoint o α) n, V ⟨α, β⟩ :=
        Finset.sum_sigma _ _ _
    _ = ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) *
            partition (endpoint o α) e s n := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [partition, Finset.mul_sum]
    _ = ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) * partition o e s n := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [partition_eq_of_up_eq (hup α hα) e s n]
    _ = partition o e s m * partition o e s n := (Finset.sum_mul _ _ _).symm
theorem even_log_subadditive_up (e : ℂ) (s : ℝ) (p q : ℕ) :
    Real.log (partition (up 0 0) e s (2 * (p + q))) ≤
      Real.log (partition (up 0 0) e s (2 * p)) +
        Real.log (partition (up 0 0) e s (2 * q)) := by
  have hpar : ∀ α ∈ saws (up 0 0) (2 * p), (endpoint (up 0 0) α).up = (up 0 0).up := by
    intro α hα
    have hwalk : α ∈ walkLists (up 0 0) (2 * p) := (Finset.mem_filter.mp hα).1
    rw [endpoint_up_parity hwalk]
    have h2 : (2 * p) % 2 = 0 := by omega
    simp [h2]
  have hsplit := partition_split_le_same (o := up 0 0) e s (2 * p) (2 * q) hpar
  have hpos1 : 0 < partition (up 0 0) e s (2 * p) := partition_pos (up 0 0) e s (2 * p)
  have hpos2 : 0 < partition (up 0 0) e s (2 * q) := partition_pos (up 0 0) e s (2 * q)
  have hpos0 : 0 < partition (up 0 0) e s (2 * p + 2 * q) :=
    partition_pos (up 0 0) e s (2 * p + 2 * q)
  rw [show 2 * (p + q) = 2 * p + 2 * q by omega]
  calc Real.log (partition (up 0 0) e s (2 * p + 2 * q))
      ≤ Real.log (partition (up 0 0) e s (2 * p) * partition (up 0 0) e s (2 * q)) :=
        Real.log_le_log hpos0 hsplit
    _ = Real.log (partition (up 0 0) e s (2 * p)) +
          Real.log (partition (up 0 0) e s (2 * q)) :=
        Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)
lemma dn_up_flip_of_mem_neighbors {v w : Vertex} (h : w ∈ neighbors v) :
    w.up = !v.up := by
  rcases v with ⟨c, r, u⟩
  rcases w with ⟨c', r', u'⟩
  cases u <;> cases u' <;> simp [neighbors, up, down] at h ⊢
lemma dn_endpoint_up_parity {o : Vertex} {n : ℕ} {γ : List Vertex}
    (hγ : γ ∈ walkLists o n) :
    (endpoint o γ).up = if n % 2 = 0 then o.up else !o.up := by
  induction n generalizing o γ with
  | zero =>
      rw [mem_walkLists_iff] at hγ
      obtain ⟨hhead, hlen, -⟩ := hγ
      have hγ' : γ = [o] := by
        cases γ with
        | nil => simp at hhead
        | cons a t =>
            have hao : a = o := by simpa using hhead
            have ht : t = [] := by
              have h0 : t.length = 0 := by simpa using hlen
              simpa using h0
            rw [ht, hao]
      rw [hγ']
      simp [endpoint]
  | succ n ih =>
      rw [mem_walkLists_iff] at hγ
      obtain ⟨hhead, hlen, hchain⟩ := hγ
      cases γ with
      | nil => simp at hhead
      | cons a t =>
          have hao : a = o := by simpa using hhead
          cases t with
          | nil => simp at hlen
          | cons v t' =>
              rw [List.isChain_cons] at hchain
              obtain ⟨hrel, hchain'⟩ := hchain
              have hv : v ∈ neighbors a := hrel v (by simp)
              have htlen : (v :: t').length = n + 1 := by simpa using hlen
              have hδ : (v :: t') ∈ walkLists v n := by
                rw [mem_walkLists_iff]
                exact ⟨rfl, htlen, hchain'⟩
              have hend : endpoint o (a :: v :: t') = endpoint v (v :: t') := by
                unfold endpoint
                rw [List.getLastD_cons, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
                  List.getLast?_cons]
                rfl
              rw [hend, ih hδ, dn_up_flip_of_mem_neighbors hv, hao]
              by_cases hn : n % 2 = 0
              · have h1 : (n + 1) % 2 = 1 := by omega
                simp [hn, h1]
              · have h1 : (n + 1) % 2 = 0 := by omega
                simp [hn, h1]
lemma dn_partition_split_le_same {o : Vertex} (e : ℂ) (s : ℝ) (m n : ℕ)
    (hup : ∀ α ∈ saws o m, (endpoint o α).up = o.up) :
    partition o e s (m + n) ≤ partition o e s m * partition o e s n := by
  classical
  have hrho : 0 ≤ rho := by unfold rho; positivity
  let f : List Vertex → Sigma (fun _ : List Vertex => List Vertex) :=
    fun γ => ⟨γ.take (m + 1), γ.drop m⟩
  let V : Sigma (fun _ : List Vertex => List Vertex) → ℝ := fun x =>
    (rho ^ m * Real.exp (s * projection e (displacement o x.1))) *
      (rho ^ n * Real.exp (s * projection e (displacement (endpoint o x.1) x.2)))
  let W : List Vertex → ℝ := fun γ =>
    rho ^ (m + n) * Real.exp (s * projection e (displacement o γ))
  have hW : ∀ γ ∈ saws o (m + n), W γ = V (f γ) := by
    intro γ hγ
    simp only [W, V, f]
    rw [splitP_displacement hγ]
    exact splitP_weight e s m n _ _
  have hf_inj : Function.Injective f := by
    rintro γ₁ γ₂ h
    have h1 : γ₁.take (m + 1) = γ₂.take (m + 1) := congrArg Sigma.fst h
    have h2 : γ₁.drop m = γ₂.drop m := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [← splitP_take_append_drop_tail γ₁ m, ← splitP_take_append_drop_tail γ₂ m, h1, h2]
  have hsubset : (saws o (m + n)).image f ⊆
      (saws o m).sigma (fun α => saws (endpoint o α) n) := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sigma.mpr ⟨splitP_take_mem_saws hγ, splitP_drop_mem_saws hγ⟩
  have hVnonneg : ∀ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), 0 ≤ V x := by
    rintro ⟨α, β⟩ hx
    simp only [V]
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hrho m) (Real.exp_pos _).le)
      (mul_nonneg (pow_nonneg hrho n) (Real.exp_pos _).le)
  calc partition o e s (m + n)
      = ∑ γ ∈ saws o (m + n), W γ := rfl
    _ = ∑ γ ∈ saws o (m + n), V (f γ) := Finset.sum_congr rfl hW
    _ = ∑ x ∈ (saws o (m + n)).image f, V x := (Finset.sum_image hf_inj.injOn).symm
    _ ≤ ∑ x ∈ (saws o m).sigma (fun α => saws (endpoint o α) n), V x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun x hx _ => hVnonneg x hx)
    _ = ∑ α ∈ saws o m, ∑ β ∈ saws (endpoint o α) n, V ⟨α, β⟩ :=
        Finset.sum_sigma _ _ _
    _ = ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) *
            partition (endpoint o α) e s n := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [partition, Finset.mul_sum]
    _ = ∑ α ∈ saws o m,
          (rho ^ m * Real.exp (s * projection e (displacement o α))) * partition o e s n := by
        apply Finset.sum_congr rfl
        intro α hα
        rw [partition_eq_of_up_eq (hup α hα) e s n]
    _ = partition o e s m * partition o e s n := (Finset.sum_mul _ _ _).symm
lemma even_log_subadditive_down (e : ℂ) (s : ℝ) (p q : ℕ) :
    Real.log (partition (down 0 0) e s (2 * (p + q))) ≤
      Real.log (partition (down 0 0) e s (2 * p)) +
        Real.log (partition (down 0 0) e s (2 * q)) := by
  have hpar : ∀ α ∈ saws (down 0 0) (2 * p),
      (endpoint (down 0 0) α).up = (down 0 0).up := by
    intro α hα
    have hwalk : α ∈ walkLists (down 0 0) (2 * p) := (Finset.mem_filter.mp hα).1
    rw [dn_endpoint_up_parity hwalk]
    have h2 : (2 * p) % 2 = 0 := by omega
    simp [h2]
  have hsplit := dn_partition_split_le_same (o := down 0 0) e s (2 * p) (2 * q) hpar
  have hpos1 : 0 < partition (down 0 0) e s (2 * p) := partition_pos (down 0 0) e s (2 * p)
  have hpos2 : 0 < partition (down 0 0) e s (2 * q) := partition_pos (down 0 0) e s (2 * q)
  have hpos0 : 0 < partition (down 0 0) e s (2 * p + 2 * q) :=
    partition_pos (down 0 0) e s (2 * p + 2 * q)
  rw [show 2 * (p + q) = 2 * p + 2 * q by omega]
  calc Real.log (partition (down 0 0) e s (2 * p + 2 * q))
      ≤ Real.log (partition (down 0 0) e s (2 * p) *
          partition (down 0 0) e s (2 * q)) :=
        Real.log_le_log hpos0 hsplit
    _ = Real.log (partition (down 0 0) e s (2 * p)) +
          Real.log (partition (down 0 0) e s (2 * q)) :=
        Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)
def logPartition (o : Vertex) (e : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log (partition o e s n) / (n : ℝ)

def freeEnergy (o : Vertex) (e : ℂ) (s : ℝ) : ℝ :=
  Filter.limUnder atTop (logPartition o e s)

theorem glue_even_odd (u : ℕ → ℝ) (l : Filter ℝ)
    (he : Tendsto (fun p : ℕ => u (2 * p)) atTop l)
    (ho : Tendsto (fun p : ℕ => u (2 * p + 1)) atTop l) :
    Tendsto u atTop l := by
  rw [tendsto_atTop'] at he ho ⊢
  intro s hs
  obtain ⟨N0, hN0⟩ := he s hs
  obtain ⟨N1, hN1⟩ := ho s hs
  refine ⟨2 * max N0 N1, ?_⟩
  intro n hn
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    exact hN0 k (by omega)
  · subst hk
    exact hN1 k (by omega)
theorem glue_logPartition_converges (c : Vertex) (e : ℂ) (s : ℝ)
    (hsub : ∀ p q : ℕ, Real.log (partition c e s (2 * (p + q))) ≤
      Real.log (partition c e s (2 * p)) + Real.log (partition c e s (2 * q)))
    (hbdd : BddBelow (Set.range (fun p : ℕ =>
      Real.log (partition c e s (2 * p)) / (p : ℝ)))) :
    ∃ A : ℝ, Tendsto (logPartition c e s) atTop (𝓝 A) := by
  classical
  let u : ℕ → ℝ := fun p => Real.log (partition c e s (2 * p))
  let evenLog : ℕ → ℝ := fun p => logPartition c e s (2 * p)
  let M : ℝ := max (partition (up 0 0) e s 1) (partition (down 0 0) e s 1)
  let L : ℝ := Real.log M
  have hsubu : Subadditive u := fun p q => hsub p q
  let A : ℝ := hsubu.lim
  have hMpos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le (partition_pos (up 0 0) e s 1) (le_max_left _ _)
  have hfk : Tendsto (fun p : ℕ => u p / (p : ℝ)) atTop (𝓝 A) := by
    have := hsubu.tendsto_lim (u := u) hbdd
    simpa [A] using this
  have heven : Tendsto evenLog atTop (𝓝 (A / 2)) := by
    have h := hfk.div_const 2
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with p hp
    dsimp [evenLog, u]
    rw [div_div]
    congr 1
    push_cast
    ring
  have hsplit_up : ∀ p : ℕ, partition c e s (2 * p + 1) ≤ partition c e s (2 * p) * M := by
    intro p
    have h := partition_split_le c e s (2 * p) 1
    simpa [M] using h
  have hsplit_low : ∀ p : ℕ,
      partition c e s (2 * (p + 1)) ≤ partition c e s (2 * p + 1) * M := by
    intro p
    have h := partition_split_le c e s (2 * p + 1) 1
    have h' : (2 * p + 1) + 1 = 2 * (p + 1) := by omega
    rw [h'] at h
    simpa [M] using h
  let q : ℕ → ℝ := fun p => ((2 * p : ℕ) : ℝ) / (((2 * p + 1 : ℕ) : ℝ))
  let r : ℕ → ℝ := fun p => ((2 * (p + 1) : ℕ) : ℝ) / (((2 * p + 1 : ℕ) : ℝ))
  let d : ℕ → ℝ := fun p => (1 : ℝ) / (((2 * p + 1 : ℕ) : ℝ))
  have hDpos : ∀ p : ℕ, (0 : ℝ) < (((2 * p + 1 : ℕ) : ℝ)) := by
    intro p
    have h : (0 : ℕ) < 2 * p + 1 := by omega
    exact_mod_cast h
  have hupper_bound : ∀ᶠ p : ℕ in atTop,
      logPartition c e s (2 * p + 1) ≤
        evenLog p * q p + L / (((2 * p + 1 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with p hp
    have hp2 : ((2 * p : ℕ) : ℝ) ≠ 0 := by
      have h : (2 * p : ℕ) ≠ 0 := by omega
      exact_mod_cast h
    have hD : (((2 * p + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (hDpos p)
    have hlog : Real.log (partition c e s (2 * p + 1)) ≤
        Real.log (partition c e s (2 * p)) + L := by
      have hle := Real.log_le_log (partition_pos c e s (2 * p + 1)) (hsplit_up p)
      have hlogmul : Real.log (partition c e s (2 * p) * M) =
          Real.log (partition c e s (2 * p)) + L := by
        rw [Real.log_mul (ne_of_gt (partition_pos c e s (2 * p))) (ne_of_gt hMpos)]
      linarith
    calc
      logPartition c e s (2 * p + 1)
          = Real.log (partition c e s (2 * p + 1)) / (((2 * p + 1 : ℕ) : ℝ)) := rfl
      _ ≤ (Real.log (partition c e s (2 * p)) + L) / (((2 * p + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = evenLog p * q p + L / (((2 * p + 1 : ℕ) : ℝ)) := by
          dsimp [evenLog, q, logPartition]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          field_simp [hp2, hD]
  have hlower_bound : ∀ᶠ p : ℕ in atTop,
      evenLog (p + 1) * r p - L / (((2 * p + 1 : ℕ) : ℝ)) ≤
        logPartition c e s (2 * p + 1) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with p hp
    have hpE : ((2 * (p + 1) : ℕ) : ℝ) ≠ 0 := by
      have h : (2 * (p + 1) : ℕ) ≠ 0 := by omega
      exact_mod_cast h
    have hD : (((2 * p + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (hDpos p)
    have hlog : Real.log (partition c e s (2 * p + 1)) ≥
        Real.log (partition c e s (2 * (p + 1))) - L := by
      have hle := Real.log_le_log (partition_pos c e s (2 * (p + 1))) (hsplit_low p)
      have hlogmul : Real.log (partition c e s (2 * p + 1) * M) =
          Real.log (partition c e s (2 * p + 1)) + L := by
        rw [Real.log_mul (ne_of_gt (partition_pos c e s (2 * p + 1))) (ne_of_gt hMpos)]
      linarith
    calc
      evenLog (p + 1) * r p - L / (((2 * p + 1 : ℕ) : ℝ))
          = (Real.log (partition c e s (2 * (p + 1))) - L) / (((2 * p + 1 : ℕ) : ℝ)) := by
          dsimp [evenLog, r, logPartition]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          field_simp [hpE, hD]
      _ ≤ Real.log (partition c e s (2 * p + 1)) / (((2 * p + 1 : ℕ) : ℝ)) := by
          gcongr
      _ = logPartition c e s (2 * p + 1) := rfl
  have hφ : Tendsto (fun p : ℕ => 2 * p) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b, fun a ha => by omega⟩
  have hd : Tendsto d atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := hbase.comp hφ
    refine h.congr' ?_
    filter_upwards with p
    simp only [Function.comp_apply]
    dsimp [d]
    congr 1
    push_cast
    ring
  have hq : Tendsto q atTop (𝓝 1) := by
    have hq_eq : q = fun p : ℕ => 1 - d p := by
      funext p
      dsimp [q, d]
      have hD : (((2 * p + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (hDpos p)
      field_simp [hD]
      push_cast
      ring
    rw [hq_eq]
    simpa using (tendsto_const_nhds.sub hd)
  have hr : Tendsto r atTop (𝓝 1) := by
    have hr_eq : r = fun p : ℕ => 1 + d p := by
      funext p
      dsimp [r, d]
      have hD : (((2 * p + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt (hDpos p)
      field_simp [hD]
      push_cast
      ring
    rw [hr_eq]
    simpa using (tendsto_const_nhds.add hd)
  have hLd : Tendsto (fun p : ℕ => L / (((2 * p + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have heq : (fun p : ℕ => L / (((2 * p + 1 : ℕ) : ℝ))) =
        fun p : ℕ => L * d p := by
      funext p; rw [mul_one_div]
    rw [heq]
    simpa using Filter.Tendsto.const_mul L hd
  have hupper_tend : Tendsto (fun p : ℕ =>
      evenLog p * q p + L / (((2 * p + 1 : ℕ) : ℝ))) atTop (𝓝 (A / 2)) := by
    have h := (heven.mul hq).add hLd
    simpa using h
  have hlower_tend : Tendsto (fun p : ℕ =>
      evenLog (p + 1) * r p - L / (((2 * p + 1 : ℕ) : ℝ))) atTop (𝓝 (A / 2)) := by
    have hshift : Tendsto (fun p : ℕ => p + 1) atTop atTop := tendsto_add_atTop_nat 1
    have heven_shift : Tendsto (fun p : ℕ => evenLog (p + 1)) atTop (𝓝 (A / 2)) :=
      heven.comp hshift
    have h := (heven_shift.mul hr).sub hLd
    simpa using h
  have hodd : Tendsto (fun p : ℕ => logPartition c e s (2 * p + 1)) atTop (𝓝 (A / 2)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower_tend hupper_tend hlower_bound hupper_bound
  exact ⟨A / 2, glue_even_odd (logPartition c e s) (𝓝 (A / 2)) heven hodd⟩
theorem logPartition_tendsto (o : Vertex) (e : ℂ) (s : ℝ) :
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s)) := by
  have hex : ∃ A : ℝ, Tendsto (logPartition o e s) atTop (𝓝 A) := by
    by_cases hu : o.up = true
    · -- up class
      have hsub : ∀ p q : ℕ, Real.log (partition (up 0 0) e s (2 * (p + q))) ≤
          Real.log (partition (up 0 0) e s (2 * p)) +
            Real.log (partition (up 0 0) e s (2 * q)) :=
        fun p q => even_log_subadditive_up e s p q
      have hbdd : BddBelow (Set.range (fun p : ℕ =>
          Real.log (partition (up 0 0) e s (2 * p)) / (p : ℝ))) :=
        even_log_bddBelow_up e s
      obtain ⟨A, hA⟩ := glue_logPartition_converges (up 0 0) e s hsub hbdd
      refine ⟨A, ?_⟩
      have hpe : partition o e s = partition (up 0 0) e s := by
        funext n
        exact partition_eq_of_up_eq (by simpa [up] using hu) e s n
      have hlog : logPartition (up 0 0) e s = logPartition o e s := by
        funext n
        show Real.log (partition (up 0 0) e s n) / (n : ℝ) =
          Real.log (partition o e s n) / (n : ℝ)
        rw [show partition (up 0 0) e s n = partition o e s n from (congrFun hpe n).symm]
      exact hlog ▸ hA
    · -- down class
      have hfalse : o.up = false := by
        cases h : o.up with
        | false => rfl
        | true => exact absurd h hu
      have hsub : ∀ p q : ℕ, Real.log (partition (down 0 0) e s (2 * (p + q))) ≤
          Real.log (partition (down 0 0) e s (2 * p)) +
            Real.log (partition (down 0 0) e s (2 * q)) :=
        fun p q => even_log_subadditive_down e s p q
      have hbdd : BddBelow (Set.range (fun p : ℕ =>
          Real.log (partition (down 0 0) e s (2 * p)) / (p : ℝ))) :=
        even_log_bddBelow_down e s
      obtain ⟨A, hA⟩ := glue_logPartition_converges (down 0 0) e s hsub hbdd
      refine ⟨A, ?_⟩
      have hpe : partition o e s = partition (down 0 0) e s := by
        funext n
        exact partition_eq_of_up_eq (by simpa [down] using hfalse) e s n
      have hlog : logPartition (down 0 0) e s = logPartition o e s := by
        funext n
        show Real.log (partition (down 0 0) e s n) / (n : ℝ) =
          Real.log (partition o e s n) / (n : ℝ)
        rw [show partition (down 0 0) e s n = partition o e s n from (congrFun hpe n).symm]
      exact hlog ▸ hA
  exact tendsto_nhds_limUnder hex
end HoneycombForce

end

end OAI
