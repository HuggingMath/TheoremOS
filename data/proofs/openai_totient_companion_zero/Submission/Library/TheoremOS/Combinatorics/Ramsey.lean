import Mathlib

/-!
# Graph Ramsey numbers

`RamseyGraph s t V` says every simple graph on `V` has an `s`-clique or an independent set of size
`t`; `ramseyNumber s t` is the least `N` with `RamseyGraph s t (Fin N)`. Contents: transfer along
embeddings and cardinality, symmetry, monotonicity in `s` and `t`, the values for `s ≤ 2`, the
Erdős–Szekeres step `R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)`, the bound `R(s+1,t+1) ≤ C(s+t,s)`, the
diagonal bound `R(k+1,k+1) ≤ 4^k`, and the characterization by `cliqueNum` and `indepNum`.

Sources: P. Erdős and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935);
R. L. Graham, B. L. Rothschild and J. H. Spencer, *Ramsey Theory*, 2nd ed., Wiley, 1990,
Section 4.1; S. Jukna, *Extremal Combinatorics*, 2nd ed., Springer, 2011, Section 4.1. Textbook
material; nothing here is specific to a benchmark problem.

Bridges: a statement `∀ G : SimpleGraph (Fin N), (∃ A, G.IsNClique s A) ∨ (∃ B, G.IsNIndepSet t B)`
is `RamseyGraph s t (Fin N)` by `Iff.rfl`; with `Gᶜ.IsNClique t B` instead, rewrite
by `isNClique_compl` (`ramseyGraph_iff_compl`). A Ramsey number defined as
`sInf {N | RamseyProperty s t N}` is `ramseyNumber s t` once the property is identified.
-/

namespace TheoremOS.Combinatorics

open Finset SimpleGraph

/-- Every graph on `V` has an `s`-clique or an independent set of size `t`. -/
def RamseyGraph (s t : ℕ) (V : Type*) : Prop :=
  ∀ G : SimpleGraph V, (∃ A : Finset V, G.IsNClique s A) ∨ ∃ B : Finset V, G.IsNIndepSet t B

theorem ramseyGraph_iff_compl (s t : ℕ) (V : Type*) :
    RamseyGraph s t V ↔
      ∀ G : SimpleGraph V,
        (∃ A : Finset V, G.IsNClique s A) ∨ ∃ B : Finset V, Gᶜ.IsNClique t B := by
  simp only [RamseyGraph, isNClique_compl]

section Transfer

variable {V W : Type*}

/-- A clique of a pulled-back graph maps to a clique. -/
theorem isNClique_map_of_comap {G : SimpleGraph W} (f : V ↪ W) {n : ℕ} {A : Finset V}
    (h : (G.comap f).IsNClique n A) : G.IsNClique n (A.map f) := by
  refine ⟨?_, by rw [Finset.card_map, h.card_eq]⟩
  intro x hx y hy hxy
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact h.isClique ha hb fun hab => hxy (congrArg f hab)

/-- An independent set of a pulled-back graph maps to an independent set. -/
theorem isNIndepSet_map_of_comap {G : SimpleGraph W} (f : V ↪ W) {n : ℕ} {B : Finset V}
    (h : (G.comap f).IsNIndepSet n B) : G.IsNIndepSet n (B.map f) := by
  refine ⟨?_, by rw [Finset.card_map, h.card_eq]⟩
  intro x hx y hy hxy
  simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact h.isIndepSet ha hb fun hab => hxy (congrArg f hab)

/-- `RamseyGraph` pulls back along embeddings. -/
theorem RamseyGraph.of_embedding {s t : ℕ} (h : RamseyGraph s t V) (f : V ↪ W) :
    RamseyGraph s t W := by
  intro G
  rcases h (G.comap f) with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact Or.inl ⟨A.map f, isNClique_map_of_comap f hA⟩
  · exact Or.inr ⟨B.map f, isNIndepSet_map_of_comap f hB⟩

theorem RamseyGraph.of_card_le [Fintype V] [Fintype W] {s t : ℕ} (h : RamseyGraph s t V)
    (hc : Fintype.card V ≤ Fintype.card W) : RamseyGraph s t W :=
  h.of_embedding (Function.Embedding.nonempty_of_card_le hc).some

theorem RamseyGraph.of_equiv {s t : ℕ} (h : RamseyGraph s t V) (e : V ≃ W) : RamseyGraph s t W :=
  h.of_embedding e.toEmbedding

theorem RamseyGraph.symm {s t : ℕ} (h : RamseyGraph s t V) : RamseyGraph t s V := by
  intro G
  rcases h Gᶜ with ⟨A, hA⟩ | ⟨B, hB⟩
  · exact Or.inr ⟨A, by simpa using hA⟩
  · exact Or.inl ⟨B, by simpa using hB⟩

theorem ramseyGraph_comm {s t : ℕ} : RamseyGraph s t V ↔ RamseyGraph t s V :=
  ⟨RamseyGraph.symm, RamseyGraph.symm⟩

/-- Monotonicity: smaller cliques and independent sets are easier to find. -/
theorem RamseyGraph.mono {s t s' t' : ℕ} (h : RamseyGraph s t V) (hs : s' ≤ s) (ht : t' ≤ t) :
    RamseyGraph s' t' V := by
  intro G
  rcases h G with ⟨A, hA⟩ | ⟨B, hB⟩
  · obtain ⟨A', hA', hc⟩ := Finset.exists_subset_card_eq (hA.card_eq ▸ hs)
    exact Or.inl ⟨A', ⟨hA.isClique.subset (by exact_mod_cast hA'), hc⟩⟩
  · obtain ⟨B', hB', hc⟩ := Finset.exists_subset_card_eq (hB.card_eq ▸ ht)
    exact Or.inr ⟨B', ⟨Set.Pairwise.mono (by exact_mod_cast hB') hB.isIndepSet, hc⟩⟩

end Transfer

section Small

variable {V : Type*}

theorem ramseyGraph_zero_left (t : ℕ) : RamseyGraph 0 t V :=
  fun _ => Or.inl ⟨∅, by simp⟩

theorem ramseyGraph_zero_right (s : ℕ) : RamseyGraph s 0 V :=
  (ramseyGraph_zero_left s).symm

theorem ramseyGraph_one_left [Nonempty V] (t : ℕ) : RamseyGraph 1 t V :=
  fun _ => Or.inl ⟨{Classical.arbitrary V}, by simp⟩

theorem ramseyGraph_one_right [Nonempty V] (s : ℕ) : RamseyGraph s 1 V :=
  (ramseyGraph_one_left s).symm

/-- The empty graph shows `RamseyGraph s t V` fails when `2 ≤ s` and `|V| < t`. -/
theorem not_ramseyGraph_of_card_lt [Fintype V] {s t : ℕ} (hs : 2 ≤ s)
    (ht : Fintype.card V < t) : ¬ RamseyGraph s t V := by
  intro h
  rcases h ⊥ with ⟨A, hA⟩ | ⟨B, hB⟩
  · have := (isNClique_bot_iff.1 hA).1
    omega
  · have := hB.card_eq ▸ Finset.card_le_univ B
    omega

theorem ramseyGraph_two_left [Fintype V] {t : ℕ} (ht : t ≤ Fintype.card V) :
    RamseyGraph 2 t V := by
  classical
  intro G
  by_cases hE : ∃ x y, G.Adj x y
  · obtain ⟨x, y, hxy⟩ := hE
    exact Or.inl ⟨{x, y}, by simp [isNClique_iff, hxy, hxy.ne, card_pair hxy.ne]⟩
  · push Not at hE
    obtain ⟨B, -, hB⟩ := Finset.exists_subset_card_eq (s := (univ : Finset V)) (by simpa using ht)
    exact Or.inr ⟨B, ⟨fun x _ y _ _ => hE x y, hB⟩⟩

theorem ramseyGraph_two_left_iff [Fintype V] {t : ℕ} :
    RamseyGraph 2 t V ↔ t ≤ Fintype.card V :=
  ⟨fun h => by by_contra hc; exact not_ramseyGraph_of_card_lt le_rfl (by omega) h,
    ramseyGraph_two_left⟩

end Small

section ErdosSzekeres

/-- The Erdős–Szekeres step: if `RamseyGraph s (t+1)` holds on `a` vertices and
`RamseyGraph (s+1) t` on `b` vertices, then `RamseyGraph (s+1) (t+1)` holds on `a + b`. -/
theorem RamseyGraph.succ_succ {V : Type*} [Fintype V] {s t a b : ℕ}
    (ha : RamseyGraph s (t + 1) (Fin a)) (hb : RamseyGraph (s + 1) t (Fin b))
    (hV : a + b ≤ Fintype.card V) (hab : 0 < a + b) : RamseyGraph (s + 1) (t + 1) V := by
  classical
  intro G
  have hne : (univ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]; omega
  obtain ⟨v, -⟩ := hne
  set A := univ.filter fun w => G.Adj v w with hA
  set B := univ.filter fun w => w ≠ v ∧ ¬ G.Adj v w with hB
  have hunion : A ∪ B = univ.erase v := by
    ext w
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    by_cases hw : G.Adj v w
    · simp [hw, hw.ne']
    · simp [hw]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    simp only [hA, hB, Finset.mem_filter, Finset.mem_univ, true_and] at hwA hwB
    exact hwB.2 hwA
  have hcard : A.card + B.card + 1 = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (mem_univ v),
      Finset.card_univ]
    have : 0 < Fintype.card V := by omega
    omega
  by_cases hAa : a ≤ A.card
  · have hT : RamseyGraph s (t + 1) A := ha.of_card_le (by simpa using hAa)
    rcases hT (G.comap (Function.Embedding.subtype (· ∈ A))) with ⟨C, hC⟩ | ⟨D, hD⟩
    · have hC' := isNClique_map_of_comap _ hC
      refine Or.inl ⟨insert v (C.map (Function.Embedding.subtype (· ∈ A))), hC'.insert ?_⟩
      intro w hw
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hw
      obtain ⟨⟨w, hwA⟩, -, rfl⟩ := hw
      simpa [hA] using hwA
    · exact Or.inr ⟨_, isNIndepSet_map_of_comap _ hD⟩
  · have hBb : b ≤ B.card := by omega
    have hT : RamseyGraph (s + 1) t B := hb.of_card_le (by simpa using hBb)
    rcases hT (G.comap (Function.Embedding.subtype (· ∈ B))) with ⟨C, hC⟩ | ⟨D, hD⟩
    · exact Or.inl ⟨_, isNClique_map_of_comap _ hC⟩
    · have hD' := isNIndepSet_map_of_comap _ hD
      rw [← isNClique_compl] at hD'
      refine Or.inr ⟨insert v (D.map (Function.Embedding.subtype (· ∈ B))), ?_⟩
      rw [← isNClique_compl]
      refine hD'.insert ?_
      intro w hw
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hw
      obtain ⟨⟨w, hwB⟩, -, rfl⟩ := hw
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hwB
      exact (compl_adj G v w).2 ⟨hwB.1.symm, hwB.2⟩

/-- `RamseyGraph (s+1) (t+1)` holds on `C(s+t, s)` vertices. -/
theorem ramseyGraph_choose (s t : ℕ) : RamseyGraph (s + 1) (t + 1) (Fin ((s + t).choose s)) := by
  induction s generalizing t with
  | zero => simpa using ramseyGraph_one_left (V := Fin 1) (t + 1)
  | succ s ihs =>
    induction t with
    | zero => simpa using ramseyGraph_one_right (V := Fin 1) (s + 1 + 1)
    | succ t iht =>
      have hA := ihs (t + 1)
      rw [show s + (t + 1) = s + t + 1 by omega] at hA
      have hB := iht
      rw [show s + 1 + t = s + t + 1 by omega] at hB
      refine RamseyGraph.succ_succ hA hB ?_ ?_
      · rw [Fintype.card_fin, show s + 1 + (t + 1) = s + t + 1 + 1 by omega,
          Nat.choose_succ_succ' (s + t + 1) s]
      · have := Nat.choose_pos (show s ≤ s + t + 1 by omega)
        omega

end ErdosSzekeres

/-- The Ramsey number: the least `N` with `RamseyGraph s t (Fin N)`. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := sInf {N | RamseyGraph s t (Fin N)}

theorem ramseyNumber_nonempty (s t : ℕ) : {N | RamseyGraph s t (Fin N)}.Nonempty := by
  rcases s with _ | s
  · exact ⟨0, ramseyGraph_zero_left t⟩
  rcases t with _ | t
  · exact ⟨0, ramseyGraph_zero_right _⟩
  exact ⟨_, ramseyGraph_choose s t⟩

theorem ramseyGraph_ramseyNumber (s t : ℕ) : RamseyGraph s t (Fin (ramseyNumber s t)) :=
  Nat.sInf_mem (ramseyNumber_nonempty s t)

theorem ramseyNumber_le_of {s t N : ℕ} (h : RamseyGraph s t (Fin N)) : ramseyNumber s t ≤ N :=
  Nat.sInf_le h

/-- `RamseyGraph s t V` holds exactly when `|V| ≥ R(s,t)`. -/
theorem ramseyGraph_iff {V : Type*} [Fintype V] {s t : ℕ} :
    RamseyGraph s t V ↔ ramseyNumber s t ≤ Fintype.card V := by
  constructor
  · intro h
    exact ramseyNumber_le_of (h.of_equiv (Fintype.equivFin V))
  · intro h
    exact (ramseyGraph_ramseyNumber s t).of_card_le (by simpa using h)

theorem ramseyGraph_fin_iff {s t N : ℕ} : RamseyGraph s t (Fin N) ↔ ramseyNumber s t ≤ N := by
  simpa using ramseyGraph_iff (V := Fin N)

theorem ramseyNumber_comm (s t : ℕ) : ramseyNumber s t = ramseyNumber t s := by
  apply le_antisymm
  · exact ramseyNumber_le_of (ramseyGraph_ramseyNumber t s).symm
  · exact ramseyNumber_le_of (ramseyGraph_ramseyNumber s t).symm

theorem ramseyNumber_mono {s t s' t' : ℕ} (hs : s' ≤ s) (ht : t' ≤ t) :
    ramseyNumber s' t' ≤ ramseyNumber s t :=
  ramseyNumber_le_of ((ramseyGraph_ramseyNumber s t).mono hs ht)

theorem ramseyNumber_zero_left (t : ℕ) : ramseyNumber 0 t = 0 :=
  Nat.eq_zero_of_le_zero (ramseyNumber_le_of (ramseyGraph_zero_left t))

theorem ramseyNumber_zero_right (s : ℕ) : ramseyNumber s 0 = 0 := by
  rw [ramseyNumber_comm, ramseyNumber_zero_left]

theorem ramseyNumber_pos {s t : ℕ} (hs : 0 < s) (ht : 0 < t) : 0 < ramseyNumber s t := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have h := ramseyGraph_ramseyNumber s t
  rw [h0] at h
  rcases h ⊥ with ⟨A, hA⟩ | ⟨B, hB⟩
  · have := hA.card_eq ▸ Finset.card_le_univ A
    simp at this; omega
  · have := hB.card_eq ▸ Finset.card_le_univ B
    simp at this; omega

theorem ramseyNumber_one_left {t : ℕ} (ht : 0 < t) : ramseyNumber 1 t = 1 :=
  le_antisymm (ramseyNumber_le_of (ramseyGraph_one_left (V := Fin 1) t))
    (ramseyNumber_pos one_pos ht)

theorem ramseyNumber_one_right {s : ℕ} (hs : 0 < s) : ramseyNumber s 1 = 1 := by
  rw [ramseyNumber_comm, ramseyNumber_one_left hs]

theorem ramseyNumber_two_left (t : ℕ) : ramseyNumber 2 t = t := by
  apply le_antisymm
  · exact ramseyNumber_le_of (ramseyGraph_two_left (by simp))
  · have := ramseyGraph_two_left_iff.1 (ramseyGraph_ramseyNumber 2 t)
    simpa using this

theorem ramseyNumber_two_right (s : ℕ) : ramseyNumber s 2 = s := by
  rw [ramseyNumber_comm, ramseyNumber_two_left]

/-- The Erdős–Szekeres recursion `R(s+1,t+1) ≤ R(s,t+1) + R(s+1,t)` (for `(s,t) ≠ (0,0)`). -/
theorem ramseyNumber_succ_succ_le {s t : ℕ} (hst : 0 < s + t) :
    ramseyNumber (s + 1) (t + 1) ≤ ramseyNumber s (t + 1) + ramseyNumber (s + 1) t := by
  have hpos : 0 < ramseyNumber s (t + 1) + ramseyNumber (s + 1) t := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · have := ramseyNumber_pos (s := 0 + 1) (t := t) (by omega) (by omega)
      omega
    · have := ramseyNumber_pos (s := s) (t := t + 1) hs (by omega)
      omega
  refine ramseyNumber_le_of (RamseyGraph.succ_succ (ramseyGraph_ramseyNumber _ _)
    (ramseyGraph_ramseyNumber _ _) (by simp) hpos)

/-- `R(s+1,t+1) ≤ C(s+t, s)`. -/
theorem ramseyNumber_le_choose (s t : ℕ) : ramseyNumber (s + 1) (t + 1) ≤ (s + t).choose s :=
  ramseyNumber_le_of (ramseyGraph_choose s t)

/-- The diagonal bound `R(k+1,k+1) ≤ 4^k`. -/
theorem ramseyNumber_diag_le (k : ℕ) : ramseyNumber (k + 1) (k + 1) ≤ 4 ^ k := by
  refine (ramseyNumber_le_choose k k).trans ?_
  rw [← two_mul]
  exact Nat.centralBinom_le_four_pow k

/-- `RamseyGraph` through clique and independence numbers. -/
theorem ramseyGraph_iff_cliqueNum {V : Type*} [Fintype V] {s t : ℕ} :
    RamseyGraph s t V ↔ ∀ G : SimpleGraph V, s ≤ G.cliqueNum ∨ t ≤ G.indepNum := by
  constructor
  · intro h G
    rcases h G with ⟨A, hA⟩ | ⟨B, hB⟩
    · exact Or.inl (hA.card_eq ▸ hA.isClique.card_le_cliqueNum)
    · exact Or.inr (hB.card_eq ▸ hB.isIndepSet.card_le_indepNum)
  · intro h
    refine RamseyGraph.mono (s := s) (t := t) ?_ le_rfl le_rfl
    intro G
    rcases h G with hs | ht
    · obtain ⟨A, hA⟩ := G.exists_isNClique_cliqueNum
      obtain ⟨A', hA', hc⟩ := Finset.exists_subset_card_eq (hA.card_eq ▸ hs)
      exact Or.inl ⟨A', ⟨hA.isClique.subset (by exact_mod_cast hA'), hc⟩⟩
    · obtain ⟨B, hB⟩ := G.exists_isNIndepSet_indepNum
      obtain ⟨B', hB', hc⟩ := Finset.exists_subset_card_eq (hB.card_eq ▸ ht)
      exact Or.inr ⟨B', ⟨Set.Pairwise.mono (by exact_mod_cast hB') hB.isIndepSet, hc⟩⟩

end TheoremOS.Combinatorics
