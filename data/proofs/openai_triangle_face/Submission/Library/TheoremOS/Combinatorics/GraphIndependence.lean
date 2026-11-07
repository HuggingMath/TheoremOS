import Mathlib

/-!
# Independent sets and colourings of finite graphs

Lower bounds for the independence number `indepNum` and upper bounds for the chromatic number of a
finite simple graph. Contents: `n ≤ k α` for a `k`-colouring, hence `n ≤ χ α`; greedy colouring
with `Δ + 1` colours; the Caro–Wei bound `∑ v, 1/(d(v)+1) ≤ α` (and its version inside a vertex
set); the Turán form `n² / (2|E| + n) ≤ α`; `n ≤ (Δ + 1) α`; and `Δ ≤ α` for triangle-free
graphs.

Sources: Y. Caro, New results on the independence number, Tel Aviv Univ. tech. report (1979);
V. K. Wei, A lower bound on the stability number of a simple graph, Bell Labs memo (1981);
N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, Section 6.1 (Turán);
R. Diestel, *Graph Theory*, 5th ed., Springer, 2017, Section 5.2 (greedy colouring). Textbook
material; nothing here is specific to a benchmark problem.

Bridges: `card_div_averageDegree_succ_le_indepNum` is `n / (d + 1) ≤ α` with the average degree
`d = 2|E| / n` written out. On a finite graph `G.chromaticNumber.toNat` is the chromatic number
(`chromaticNumber_ne_top`), as in `card_le_chromaticNumber_toNat_mul_indepNum`.
-/

namespace TheoremOS.Combinatorics

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

section Colouring

/-- A `k`-colouring has a colour class of size `≥ n/k`: `n ≤ k α`. -/
theorem card_le_mul_indepNum_of_coloring {α : Type*} [Fintype α] (C : G.Coloring α) :
    Fintype.card V ≤ Fintype.card α * G.indepNum := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := C) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (mem_univ _))]
  calc ∑ c, #{v ∈ (univ : Finset V) | C v = c} ≤ ∑ _c : α, G.indepNum :=
        Finset.sum_le_sum fun c _ => IsIndepSet.card_le_indepNum fun x hx y hy hxy hadj => by
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
          exact C.valid hadj (hx.trans hy.symm)
    _ = Fintype.card α * G.indepNum := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem card_le_mul_indepNum_of_colorable {k : ℕ} (h : G.Colorable k) :
    Fintype.card V ≤ k * G.indepNum := by
  simpa using card_le_mul_indepNum_of_coloring G h.some

/-- `n ≤ χ α`. -/
theorem card_le_chromaticNumber_toNat_mul_indepNum :
    Fintype.card V ≤ G.chromaticNumber.toNat * G.indepNum :=
  card_le_mul_indepNum_of_colorable G (colorable_chromaticNumber_of_fintype G)

theorem chromaticNumber_ne_top : G.chromaticNumber ≠ ⊤ :=
  chromaticNumber_ne_top_iff_exists.2 ⟨_, colorable_of_fintype G⟩

/-- Greedy colouring inside a vertex set: `Δ + 1` colours suffice on `S`. -/
theorem exists_coloring_on_maxDegree_succ [DecidableRel G.Adj] (S : Finset V) :
    ∃ c : V → Fin (G.maxDegree + 1), ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | @insert v S hvS ih =>
    obtain ⟨c, hc⟩ := ih
    have hlt : #((S.filter (G.Adj v)).image c) < #(univ : Finset (Fin (G.maxDegree + 1))) := by
      calc #((S.filter (G.Adj v)).image c) ≤ #(S.filter (G.Adj v)) := card_image_le
        _ ≤ #(G.neighborFinset v) := card_le_card fun w hw => by
            rw [mem_neighborFinset]; exact (mem_filter.1 hw).2
        _ = G.degree v := card_neighborFinset_eq_degree G v
        _ ≤ G.maxDegree := G.degree_le_maxDegree v
        _ < #(univ : Finset (Fin (G.maxDegree + 1))) := by simp
    obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Function.update c v a, fun x hx y hy hxy => ?_⟩
    rw [mem_insert] at hx hy
    have hxv : ∀ {w}, w ∈ S → w ≠ v := fun hw h => hvS (h ▸ hw)
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact (G.irrefl hxy).elim
    · rw [Function.update_self, Function.update_of_ne (hxv hy)]
      exact fun h => ha (h ▸ mem_image_of_mem c (mem_filter.2 ⟨hy, hxy⟩))
    · rw [Function.update_self, Function.update_of_ne (hxv hx)]
      exact fun h => ha (h.symm ▸ mem_image_of_mem c (mem_filter.2 ⟨hx, hxy.symm⟩))
    · rw [Function.update_of_ne (hxv hx), Function.update_of_ne (hxv hy)]
      exact hc x hx y hy hxy

/-- Greedy colouring: every finite graph is `(Δ + 1)`-colourable. -/
theorem colorable_maxDegree_succ [DecidableRel G.Adj] : G.Colorable (G.maxDegree + 1) := by
  obtain ⟨c, hc⟩ := exists_coloring_on_maxDegree_succ G univ
  exact ⟨Coloring.mk c fun h => hc _ (mem_univ _) _ (mem_univ _) h⟩

theorem chromaticNumber_le_maxDegree_succ [DecidableRel G.Adj] :
    G.chromaticNumber ≤ G.maxDegree + 1 := by
  exact_mod_cast (colorable_maxDegree_succ G).chromaticNumber_le

theorem chromaticNumber_toNat_le_maxDegree_succ [DecidableRel G.Adj] :
    G.chromaticNumber.toNat ≤ G.maxDegree + 1 :=
  ENat.toNat_le_of_le_natCast (by exact_mod_cast chromaticNumber_le_maxDegree_succ G)

/-- `n ≤ (Δ + 1) α`. -/
theorem card_le_maxDegree_succ_mul_indepNum [DecidableRel G.Adj] :
    Fintype.card V ≤ (G.maxDegree + 1) * G.indepNum :=
  card_le_mul_indepNum_of_colorable G (colorable_maxDegree_succ G)

end Colouring

section CaroWei

variable [DecidableRel G.Adj]

omit [Fintype V] in
/-- Caro–Wei inside a vertex set: `S` contains an independent set of size at least
`∑ v ∈ S, 1 / (d_S(v) + 1)`, where `d_S(v)` counts the neighbours of `v` in `S`. -/
theorem exists_isIndepSet_sum_le (S : Finset V) :
    ∃ I ⊆ S, G.IsIndepSet (I : Set V) ∧
      ∑ v ∈ S, (1 : ℝ) / (#{w ∈ S | G.Adj v w} + 1) ≤ #I := by
  classical
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, Finset.Subset.rfl, by simp, by simp⟩
  obtain ⟨v, hvS, hmin⟩ := S.exists_min_image (fun u => #{w ∈ S | G.Adj u w}) hne
  have hS'S : S.filter (fun w => ¬(w = v ∨ G.Adj v w)) ⊂ S :=
    filter_ssubset.2 ⟨v, hvS, fun h => h (Or.inl rfl)⟩
  obtain ⟨I, hIS, hI, hIsum⟩ := ih _ hS'S
  have hvI : v ∉ I := fun h => (mem_filter.1 (hIS h)).2 (Or.inl rfl)
  refine ⟨insert v I, insert_subset hvS (hIS.trans (filter_subset _ _)), ?_, ?_⟩
  · rw [coe_insert]
    refine hI.insert_of_notMem (by simpa using hvI) fun b hb => ?_
    have hb' := (mem_filter.1 (hIS hb)).2
    exact ⟨fun h => hb' (Or.inr h), fun h => hb' (Or.inr h.symm)⟩
  have hcardN : #{w ∈ S | w = v ∨ G.Adj v w} = #{w ∈ S | G.Adj v w} + 1 := by
    have : ({w ∈ S | w = v ∨ G.Adj v w} : Finset V) = insert v {w ∈ S | G.Adj v w} := by
      ext w
      by_cases hw : w = v
      · subst hw; simp [hvS]
      · simp [hw]
    rw [this, card_insert_of_notMem (by simp)]
  have hN : ∑ u ∈ S with u = v ∨ G.Adj v u, (1 : ℝ) / (#{w ∈ S | G.Adj u w} + 1) ≤ 1 := by
    calc ∑ u ∈ S with u = v ∨ G.Adj v u, (1 : ℝ) / (#{w ∈ S | G.Adj u w} + 1)
        ≤ ∑ u ∈ S with u = v ∨ G.Adj v u, (1 : ℝ) / (#{w ∈ S | G.Adj v w} + 1) := by
          refine sum_le_sum fun u hu => one_div_le_one_div_of_le (by positivity) ?_
          exact_mod_cast Nat.add_le_add_right (hmin u (mem_filter.1 hu).1) 1
      _ = 1 := by
          rw [sum_const, hcardN, nsmul_eq_mul]
          push_cast
          field_simp
  have hS' : ∑ u ∈ S with ¬(u = v ∨ G.Adj v u), (1 : ℝ) / (#{w ∈ S | G.Adj u w} + 1) ≤ #I := by
    refine le_trans (sum_le_sum fun u _ => ?_) hIsum
    have hc : #{w ∈ S.filter (fun w => ¬(w = v ∨ G.Adj v w)) | G.Adj u w}
        ≤ #{w ∈ S | G.Adj u w} := card_le_card (filter_subset_filter _ (filter_subset _ _))
    gcongr
  have hsplit := sum_filter_add_sum_filter_not S (fun u => u = v ∨ G.Adj v u)
    (fun u => (1 : ℝ) / (#{w ∈ S | G.Adj u w} + 1))
  beta_reduce at hsplit
  rw [card_insert_of_notMem hvI, Nat.cast_add, Nat.cast_one]
  linarith

/-- The Caro–Wei bound `∑ v, 1 / (d(v) + 1) ≤ α`. -/
theorem sum_one_div_degree_succ_le_indepNum :
    ∑ v, (1 : ℝ) / (G.degree v + 1) ≤ G.indepNum := by
  obtain ⟨I, -, hI, hsum⟩ := exists_isIndepSet_sum_le G univ
  have hdeg : ∀ v, G.degree v = #{w ∈ (univ : Finset V) | G.Adj v w} := fun v => by
    rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
  simp_rw [hdeg]
  exact hsum.trans (by exact_mod_cast hI.card_le_indepNum)

/-- Turán's bound in Caro–Wei form: `n² / (2|E| + n) ≤ α`. -/
theorem card_sq_div_le_indepNum :
    (Fintype.card V : ℝ) ^ 2 / (2 * #G.edgeFinset + Fintype.card V) ≤ G.indepNum := by
  refine le_trans ?_ (sum_one_div_degree_succ_le_indepNum G)
  have h := sq_sum_div_le_sum_sq_div (univ : Finset V) (fun _ => (1 : ℝ))
    (g := fun v => (G.degree v : ℝ) + 1) fun v _ => by positivity
  have hsum : ∑ v, ((G.degree v : ℝ) + 1) = 2 * #G.edgeFinset + Fintype.card V := by
    rw [sum_add_distrib, ← Nat.cast_sum, sum_degrees_eq_twice_card_edges]
    simp
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, one_pow] at h
  rwa [hsum] at h

/-- The same bound with the average degree `d = 2|E| / n`: `n / (d + 1) ≤ α`. -/
theorem card_div_averageDegree_succ_le_indepNum :
    (Fintype.card V : ℝ) / (2 * #G.edgeFinset / Fintype.card V + 1) ≤ G.indepNum := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hpos
  · simp [h0]
  have hn : (Fintype.card V : ℝ) ≠ 0 := by positivity
  rw [div_add_one hn, div_div_eq_mul_div, ← sq]
  exact card_sq_div_le_indepNum G

end CaroWei

section TriangleFree

variable [DecidableRel G.Adj]

/-- In a triangle-free graph every neighbourhood is independent: `d(v) ≤ α`. -/
theorem degree_le_indepNum_of_cliqueFree_three (h : G.CliqueFree 3) (v : V) :
    G.degree v ≤ G.indepNum := by
  rw [← card_neighborFinset_eq_degree]
  exact IsIndepSet.card_le_indepNum (by
    rw [coe_neighborFinset]; exact G.isIndepSet_neighborSet_of_triangleFree h v)

theorem maxDegree_le_indepNum_of_cliqueFree_three (h : G.CliqueFree 3) :
    G.maxDegree ≤ G.indepNum :=
  G.maxDegree_le_of_forall_degree_le _ (degree_le_indepNum_of_cliqueFree_three G h)

end TriangleFree

end TheoremOS.Combinatorics
