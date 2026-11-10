import Submission.Library.TheoremOS.Combinatorics.Ramsey
import Submission.Library.TheoremOS.Probability.BiasedProduct

/-!
# Erdős's lower bound for diagonal Ramsey numbers

The random-graph argument for `R(k,k)`: a uniformly random graph on `Fin N` has an expected
`2 C(N,k) 2^{-C(k,2)}` cliques or independent sets of size `k`, so `RamseyGraph k k (Fin N)` fails
when this is `< 1`. Contents: graphs from sets of 2-subsets (`graphOfEdges`), the edges inside a
vertex set (`edgesIn`, `C(|A|,2)` of them), the union bound `not_ramseyGraph_of_lt_one`, and the
classical corollary `N ^ 2 ≤ 2 ^ k → N < R(k,k)` for `k ≥ 3`, i.e. `2^{k/2} < R(k,k)`.

Sources: P. Erdős, Some remarks on the theory of graphs, Bull. Amer. Math. Soc. 53 (1947);
N. Alon and J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, Section 1.1. Textbook
material; nothing here is specific to a benchmark problem.

Bridges: the probability space is `biasedMass (1/2)` on `Finset (GraphEdge N)` with
`GraphEdge N = {e : Finset (Fin N) // e.card = 2}`; combine `ramseyNumber_gt_of_sq_le` with
`ramseyGraph_fin_iff` to move between the predicate and the number.
-/

namespace TheoremOS.Combinatorics

open Finset TheoremOS.Probability

/-- The 2-subsets of `Fin N`, the possible edges of a graph on `Fin N`. -/
abbrev GraphEdge (N : ℕ) := {e : Finset (Fin N) // e.card = 2}

/-- The graph whose edges are the 2-subsets in `s`. -/
def graphOfEdges {N : ℕ} (s : Finset (GraphEdge N)) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ ∃ e ∈ s, (e : Finset (Fin N)) = {x, y}
  symm.symm x y h :=
    ⟨h.1.symm, by obtain ⟨e, he, hxy⟩ := h.2; exact ⟨e, he, by rw [hxy, pair_comm]⟩⟩
  loopless.irrefl x h := h.1 rfl

theorem graphOfEdges_adj {N : ℕ} (s : Finset (GraphEdge N)) (x y : Fin N) :
    (graphOfEdges s).Adj x y ↔ x ≠ y ∧ ∃ e ∈ s, (e : Finset (Fin N)) = {x, y} := Iff.rfl

/-- The edges inside a vertex set. -/
def edgesIn {N : ℕ} (A : Finset (Fin N)) : Finset (GraphEdge N) :=
  univ.filter fun e => (e : Finset (Fin N)) ⊆ A

theorem card_edgesIn {N : ℕ} (A : Finset (Fin N)) : (edgesIn A).card = A.card.choose 2 := by
  rw [← card_powersetCard]
  refine Finset.card_bij (fun e _ => (e : Finset (Fin N))) ?_ ?_ ?_
  · intro e he
    simp only [edgesIn, mem_filter, mem_univ, true_and] at he
    exact mem_powersetCard.2 ⟨he, e.2⟩
  · intro e₁ _ e₂ _ h
    exact Subtype.ext h
  · intro t ht
    obtain ⟨hA, hc⟩ := mem_powersetCard.1 ht
    exact ⟨⟨t, hc⟩, by simpa [edgesIn] using hA, rfl⟩

theorem edgesIn_subset_of_isClique {N : ℕ} {s : Finset (GraphEdge N)} {A : Finset (Fin N)}
    (h : (graphOfEdges s).IsClique (A : Set (Fin N))) : edgesIn A ⊆ s := by
  intro e he
  simp only [edgesIn, mem_filter, mem_univ, true_and] at he
  obtain ⟨x, y, hxy, hexy⟩ := card_eq_two.1 e.2
  have hx : x ∈ A := he (by rw [hexy]; simp)
  have hy : y ∈ A := he (by rw [hexy]; simp)
  obtain ⟨-, e', he', he'xy⟩ := (graphOfEdges_adj s x y).1 (h hx hy hxy)
  rwa [show e = e' from Subtype.ext (hexy.trans he'xy.symm)]

theorem edgesIn_subset_compl_of_isIndepSet {N : ℕ} {s : Finset (GraphEdge N)}
    {A : Finset (Fin N)} (h : (graphOfEdges s).IsIndepSet (A : Set (Fin N))) :
    edgesIn A ⊆ sᶜ := by
  intro e he
  simp only [edgesIn, mem_filter, mem_univ, true_and] at he
  rw [mem_compl]
  intro hes
  obtain ⟨x, y, hxy, hexy⟩ := card_eq_two.1 e.2
  have hx : x ∈ A := he (by rw [hexy]; simp)
  have hy : y ∈ A := he (by rw [hexy]; simp)
  exact h hx hy hxy ((graphOfEdges_adj s x y).2 ⟨hxy, e, hes, hexy⟩)

/-- The union bound: if `2 C(N,k) 2^{-C(k,2)} < 1` then some graph on `Fin N` has neither a
`k`-clique nor an independent set of size `k`. -/
theorem not_ramseyGraph_of_lt_one {N k : ℕ}
    (hlt : 2 * (N.choose k : ℝ) * (1 / 2) ^ k.choose 2 < 1) : ¬ RamseyGraph k k (Fin N) := by
  classical
  intro hR
  set 𝒜 := (univ : Finset (Fin N)).powersetCard k with h𝒜
  have hpt : ∀ s : Finset (GraphEdge N), (1 : ℝ) ≤
      ∑ A ∈ 𝒜, ((if edgesIn A ⊆ s then 1 else 0) + if Disjoint s (edgesIn A) then 1 else 0) := by
    intro s
    rcases hR (graphOfEdges s) with ⟨A, hA⟩ | ⟨A, hA⟩
    · have hA𝒜 : A ∈ 𝒜 := mem_powersetCard.2 ⟨subset_univ _, hA.card_eq⟩
      refine le_trans ?_ (Finset.single_le_sum (f := fun A =>
        ((if edgesIn A ⊆ s then (1 : ℝ) else 0) + if Disjoint s (edgesIn A) then 1 else 0))
        (fun A _ => by positivity) hA𝒜)
      rw [ite_eq_left (edgesIn_subset_of_isClique hA.isClique)]
      split_ifs <;> norm_num
    · have hA𝒜 : A ∈ 𝒜 := mem_powersetCard.2 ⟨subset_univ _, hA.card_eq⟩
      refine le_trans ?_ (Finset.single_le_sum (f := fun A =>
        ((if edgesIn A ⊆ s then (1 : ℝ) else 0) + if Disjoint s (edgesIn A) then 1 else 0))
        (fun A _ => by positivity) hA𝒜)
      have hd : Disjoint s (edgesIn A) :=
        disjoint_comm.1 (subset_compl_iff_disjoint_right.1 (edgesIn_subset_compl_of_isIndepSet
          hA.isIndepSet))
      rw [ite_eq_left hd]
      split_ifs <;> norm_num
  have h1 : (1 : ℝ) ≤ 2 * (N.choose k : ℝ) * (1 / 2) ^ k.choose 2 := by
    calc (1 : ℝ) = ∑ s, biasedMass (1 / 2) s * 1 := by simp [sum_biasedMass]
      _ ≤ ∑ s, biasedMass (1 / 2) s * ∑ A ∈ 𝒜, ((if edgesIn A ⊆ s then 1 else 0) +
            if Disjoint s (edgesIn A) then 1 else 0) :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpt s)
            (biasedMass_nonneg (by norm_num) (by norm_num) s)
      _ = ∑ A ∈ 𝒜, ((∑ s with edgesIn A ⊆ s, biasedMass (1 / 2) s) +
            ∑ s with Disjoint s (edgesIn A), biasedMass (1 / 2) s) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs <;> ring
      _ = 2 * (N.choose k : ℝ) * (1 / 2) ^ k.choose 2 := by
          rw [Finset.sum_congr rfl fun A hA => by
            rw [sum_biasedMass_superset, sum_biasedMass_disjoint, card_edgesIn,
              (mem_powersetCard.1 hA).2]]
          rw [Finset.sum_const, h𝒜, card_powersetCard, card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          norm_num
          ring
  linarith

theorem two_pow_lt_factorial_sq {k : ℕ} (hk : 3 ≤ k) : 2 ^ (k + 2) < (k.factorial) ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    have : 2 ≤ (k + 1) ^ 2 := by nlinarith
    calc 2 ^ (k + 2) * 2 < (k.factorial) ^ 2 * 2 := by omega
      _ ≤ (k.factorial) ^ 2 * (k + 1) ^ 2 := Nat.mul_le_mul_left _ this
      _ = (k + 1) ^ 2 * (k.factorial) ^ 2 := mul_comm _ _

theorem two_mul_choose_two_add (k : ℕ) : 2 * k.choose 2 + k = k ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    nlinarith

/-- Erdős's bound: for `k ≥ 3` and `N ^ 2 ≤ 2 ^ k`, some graph on `Fin N` has neither a
`k`-clique nor an independent set of size `k`. -/
theorem not_ramseyGraph_of_sq_le {N k : ℕ} (hk : 3 ≤ k) (hN : N ^ 2 ≤ 2 ^ k) :
    ¬ RamseyGraph k k (Fin N) := by
  refine not_ramseyGraph_of_lt_one ?_
  set c := k.choose 2
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h2c : (0 : ℝ) < 2 ^ c := by positivity
  have hfac : (2 : ℝ) ^ (k + 2) < (k.factorial : ℝ) ^ 2 := by
    exact_mod_cast two_pow_lt_factorial_sq hk
  have hNk : ((N : ℝ) ^ k) ^ 2 ≤ ((2 : ℝ) ^ k) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hN) k
  have hkk : ((2 : ℝ) ^ k) ^ k = (2 ^ c) ^ 2 * 2 ^ k := by
    rw [← pow_mul, ← pow_mul, ← pow_add, show k * k = c * 2 + k by
      have := two_mul_choose_two_add k; nlinarith]
  have hsq : (2 * (N : ℝ) ^ k) ^ 2 < ((k.factorial : ℝ) * 2 ^ c) ^ 2 := by
    rw [mul_pow, mul_pow]
    rw [show (2 : ℝ) ^ (k + 2) = 2 ^ 2 * 2 ^ k by ring] at hfac
    have hb := hNk.trans_eq hkk
    nlinarith [mul_lt_mul_of_pos_left hfac (pow_pos h2c 2)]
  have hkey : 2 * (N : ℝ) ^ k < (k.factorial : ℝ) * 2 ^ c :=
    lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hch : (N.choose k : ℝ) ≤ (N : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k N
  have hinv : (1 / 2 : ℝ) ^ c * 2 ^ c = 1 := by rw [← mul_pow]; norm_num
  have hlt : 2 * (N.choose k : ℝ) < 2 ^ c := by
    have : (N : ℝ) ^ k / k.factorial < 2 ^ c / 2 := by
      rw [div_lt_div_iff₀ hf (by norm_num)]; linarith
    linarith
  nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) c]

/-- `N < R(k,k)` whenever `k ≥ 3` and `N ^ 2 ≤ 2 ^ k`; that is, `2^{k/2} < R(k,k)`. -/
theorem ramseyNumber_gt_of_sq_le {N k : ℕ} (hk : 3 ≤ k) (hN : N ^ 2 ≤ 2 ^ k) :
    N < ramseyNumber k k := by
  by_contra h
  exact not_ramseyGraph_of_sq_le hk hN (ramseyGraph_fin_iff.2 (by omega))

end TheoremOS.Combinatorics
