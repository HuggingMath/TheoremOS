import Mathlib

/-!
# Reconstruction on trees: total variation, broadcast laws and census moments

Tools for root-state reconstruction in a branching broadcast. Contents: total variation
`pmfTV p q = ½ ∑' a, |p a - q a|` between `PMF`s (symmetric, `≤ 1`, triangle inequality, the
positive-part form `pmfTV_eq_toReal_tsum_tsub`) with data processing `pmfTV_bind_le` and
`pmfTV_map_le`; the uniform mixture `pmfMixture law` and the reconstruction advantage
`reconAdvantage law`, the average over root states of `pmfTV (law i) (pmfMixture law)`, with
`0 ≤ · ≤ 1`, data processing `reconAdvantage_bind_le`, the value `1 - 1 / card ι` for direct
observation (`reconAdvantage_pure`) and `pmfTV (law i) (law j) ≤ card ι · reconAdvantage law`;
the posterior forms `∑' y, m y · (∑ i, |post y i - c|) / 2 = reconAdvantage law` for any
posterior with `m y · post y i = c · law i y` (`tsum_mul_posterior_eq_reconAdvantage`), for the
`if m y = 0 then c else …` posterior and for the `ℝ≥0∞` quotient posterior
`(c · law i y) / ∑ j, c · law j y`; antitone nonnegative sequences converge to their infimum and
have a positive limit iff they are bounded below by a positive constant (also with an eventual
bound); independent draws `iidList p k`, entrywise kernels `listTraverse` and
`multisetTraverse`, `iidList (p.bind g) k = (iidList p k).bind (listTraverse g)` and its
multiset form; branching broadcasts `IsBroadcastLaw K N leaf up law` on any tower of observation
types (depth `n + 1` observes the multiset of children's depth-`n` observations) with the growth
kernel `towerGrow`, `law (n + 1) i = (law n i).bind (towerGrow …)`
(`IsBroadcastLaw.succ_eq_bind`), hence antitone advantage, convergence to the infimum and the
equivalence "positive limit ↔ uniform positive lower bound" (`IsBroadcastLaw.antitone`,
`.tendsto`, `.exists_pos_tendsto_iff`), with the concrete tower `TreeObs`, `treeLaw`; the Potts
channel `pottsWeight lam i j = lam·[i = j] + (1 - lam) / card ι` (row sums `1`, nonnegativity
for `-1 ≤ (card ι - 1) lam ≤ 1`, centred functions are eigenfunctions with eigenvalue `lam`,
composition multiplies eigenvalues, the `Fin 3` values, `pottsPMF`); the second-moment
distinguisher `(E_p S - E_q S)^2 ≤ 2 pmfTV p q (E_p (S - c)^2 + E_q (S - c)^2)`
(`sq_sub_le_pmfTV_mul_centred`) and `E (S - c)^2 = E S^2 - 2 c E S + c^2`; in `ℝ≥0∞`, the tower
rule `tsum_bind_mul`, Wald's identities for `k` and for `N`-distributed many independent draws
(`E ∑ F = E N · E F`, `E (∑ F)(∑ H) = E N · E[F H] + E N(N - 1) · E F E H`), and for additive
statistics `X (n + 1) (up n s) = (s.map (X n)).sum` of a broadcast the one-step moment
identities `IsBroadcastLaw.tsum_mul_census` and `.tsum_mul_census_mul_census`; the Poisson mean
`d` and second factorial moment `d^2` (`hasSum_poissonWeight_mul`,
`hasSum_poissonWeight_mul_descFactorial`, `ℝ≥0∞` forms with `ENNReal.ofReal` weights). Not
included: solving the census recursions for a particular channel and offspring law, variance
bounds, or any reconstruction or non-reconstruction threshold (Kesten–Stigum or otherwise).

Sources: E. Mossel, "Survey: information flow on trees", in *Graphs, Morphisms and Statistical
Physics*, DIMACS Ser. 63, AMS, 2004, 155–170 (reconstruction problem, census statistic,
Kesten–Stigum bound); W. Evans, C. Kenyon, Y. Peres and L. J. Schulman, "Broadcasting on trees
and the Ising model", Ann. Appl. Probab. 10 (2000), 410–433; H. Kesten and B. P. Stigum,
"Additional limit theorems for indecomposable multidimensional Galton–Watson processes", Ann.
Math. Statist. 37 (1966), 1463–1481; D. A. Levin, Y. Peres and E. L. Wilmer, *Markov Chains and
Mixing Times*, AMS, 2009, Chapter 4 (total variation, data processing); K. B. Athreya and
P. E. Ney, *Branching Processes*, Springer, 1972, Chapter I (Galton–Watson moments); W. Feller,
*An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed., Wiley, 1968,
Chapters VI and XII (Poisson moments, random sums). Textbook material; nothing here is specific
to a benchmark problem.

Bridges: a local copy of `iidList` with the same two equations is the library one,
`rw [TheoremOS.Probability.iidList_eq_of_rec Local.iidList (fun _ => rfl) (fun _ _ => rfl)]`
(inside the local namespace a bare `iidList` still means the local one). For a local tower
`Observation (n + 1) := Multiset (Observation n)` with `law (n + 1) i = N.bind fun k =>
(iidList ((K i).bind (law n)) k).map …`, take `leaf := fun i => i`, `up := fun _ s => s`;
`IsBroadcastLaw` then holds by `⟨fun _ => rfl, fun n i => by rw [iidList_eq_of_rec …]; rfl⟩`
when the map is `fun xs : List _ => (xs : Multiset _)`. An untyped `fun xs ↦ (xs : Multiset _)`
elaborates to `PMF.map (fun s => s) (… >>= fun a => pure ↑a)`: after the rewrite,
`simp only [law]; congr 1; funext k; exact map_id_bind_pure_coe _`. The injectivity arguments
are `fun _ _ h => h` and `fun _ _ _ h => h`. A uniform prior `PMF.ofFintype (fun _ => 1 / 3) _`
mixes to `pmfMixture` by `bind_eq_pmfMixture _ (fun i => by simp [prior]) law`; an advantage
`∑' y, (prior.bind law y).toReal * ((∑ i, |posterior law y i - 1 / 3|) / 2)` then reduces to
`reconAdvantage law` with `tsum_mul_posterior_ite_eq_reconAdvantage law (1 / 3) (by simp)` or,
for joint/marginal weights `(1 / 3) * law i y` in `ℝ≥0∞`,
`tsum_mul_posterior_div_eq_reconAdvantage` after unfolding them (`simpa`). For an advantage
sequence `adv n = reconAdvantage (law n)` rewrite with `funext` before using
`exists_pos_tendsto_iff`. `rw` cannot turn a sum over `Observation (n + 1)` into one over
`Multiset (Observation n)` (they agree only after unfolding); the census identities take the
tower hypothesis instead. Channel weights `PMF.ofFintype (fun j => ENNReal.ofReal (w i j)) _`
have `toReal` equal to `w i j` by `simp only [channel, PMF.ofFintype_apply]` and
`ENNReal.toReal_ofReal`; a Poisson law `⟨fun k => ENNReal.ofReal (exp (-d) * d ^ k / k !), _⟩`
has `∑' k, P k * k = ENNReal.ofReal d` by `tsum_ofReal_poissonWeight_mul hd` directly.
-/

namespace TheoremOS.Probability

open Filter Finset
open scoped ENNReal

noncomputable section

section TV

variable {α β : Type*}

/-- Total variation distance between two probability mass functions,
`½ ∑' a, |p a - q a|` (values read in `ℝ`). -/
def pmfTV (p q : PMF α) : ℝ := (1 / 2 : ℝ) * ∑' a, |(p a).toReal - (q a).toReal|

theorem pmf_summable_toReal (p : PMF α) : Summable fun a => (p a).toReal :=
  ENNReal.summable_toReal (by simp)

theorem pmf_tsum_toReal (p : PMF α) : ∑' a, (p a).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe, ENNReal.toReal_one]

theorem pmf_summable_abs_sub (p q : PMF α) :
    Summable fun a => |(p a).toReal - (q a).toReal| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun a => (abs_sub _ _).trans (by
      rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]))
    ((pmf_summable_toReal p).add (pmf_summable_toReal q))

theorem pmfTV_nonneg (p q : PMF α) : 0 ≤ pmfTV p q :=
  mul_nonneg (by norm_num) (tsum_nonneg fun _ => abs_nonneg _)

theorem pmfTV_comm (p q : PMF α) : pmfTV p q = pmfTV q p := by
  simp only [pmfTV, abs_sub_comm]

@[simp] theorem pmfTV_self (p : PMF α) : pmfTV p p = 0 := by simp [pmfTV]

theorem pmfTV_le_one (p q : PMF α) : pmfTV p q ≤ 1 := by
  have h : ∑' a, |(p a).toReal - (q a).toReal| ≤ ∑' a, ((p a).toReal + (q a).toReal) :=
    (pmf_summable_abs_sub p q).tsum_le_tsum (fun a => (abs_sub _ _).trans (by
      rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]))
      ((pmf_summable_toReal p).add (pmf_summable_toReal q))
  rw [(pmf_summable_toReal p).tsum_add (pmf_summable_toReal q), pmf_tsum_toReal,
    pmf_tsum_toReal] at h
  unfold pmfTV; linarith

theorem pmfTV_triangle (p q r : PMF α) : pmfTV p r ≤ pmfTV p q + pmfTV q r := by
  have h := (pmf_summable_abs_sub p r).tsum_le_tsum
    (fun a => abs_sub_le ((p a).toReal) ((q a).toReal) ((r a).toReal))
    ((pmf_summable_abs_sub p q).add (pmf_summable_abs_sub q r))
  rw [(pmf_summable_abs_sub p q).tsum_add (pmf_summable_abs_sub q r)] at h
  unfold pmfTV; linarith

theorem toReal_tsub_pmf (p q : PMF α) (a : α) :
    (p a - q a).toReal = max ((p a).toReal - (q a).toReal) 0 := by
  rcases le_total (q a) (p a) with h | h
  · rw [ENNReal.toReal_sub_of_le h (p.apply_ne_top a), max_eq_left]
    exact sub_nonneg.2 (ENNReal.toReal_mono (p.apply_ne_top a) h)
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_zero, max_eq_right]
    exact sub_nonpos.2 (ENNReal.toReal_mono (q.apply_ne_top a) h)

theorem tsum_tsub_ne_top (p q : PMF α) : ∑' a, (p a - q a) ≠ ∞ :=
  ne_top_of_le_ne_top (by simp : ∑' a, p a ≠ ∞) (ENNReal.tsum_le_tsum fun _ => tsub_le_self)

/-- Total variation as the mass of the positive part, `∑' a, (p a - q a)` with truncated
subtraction in `ℝ≥0∞`. -/
theorem pmfTV_eq_toReal_tsum_tsub (p q : PMF α) :
    pmfTV p q = (∑' a, (p a - q a)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun a => ne_top_of_le_ne_top (p.apply_ne_top a) tsub_le_self)]
  simp only [toReal_tsub_pmf]
  have hpos : Summable fun a => max ((p a).toReal - (q a).toReal) 0 :=
    Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
      (fun a => max_le (le_abs_self _) (abs_nonneg _)) (pmf_summable_abs_sub p q)
  have hneg : Summable fun a => max ((q a).toReal - (p a).toReal) 0 :=
    Summable.of_nonneg_of_le (fun _ => le_max_right _ _)
      (fun a => max_le (by rw [abs_sub_comm]; exact le_abs_self _) (abs_nonneg _))
      (pmf_summable_abs_sub p q)
  have habs : ∀ a, |(p a).toReal - (q a).toReal| =
      max ((p a).toReal - (q a).toReal) 0 + max ((q a).toReal - (p a).toReal) 0 := by
    intro a
    rcases le_total (q a).toReal (p a).toReal with h | h
    · rw [abs_of_nonneg (sub_nonneg.2 h), max_eq_left (sub_nonneg.2 h),
        max_eq_right (sub_nonpos.2 h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.2 h), max_eq_right (sub_nonpos.2 h),
        max_eq_left (sub_nonneg.2 h)]; ring
  have hdiff : ∀ a, (p a).toReal - (q a).toReal =
      max ((p a).toReal - (q a).toReal) 0 - max ((q a).toReal - (p a).toReal) 0 := by
    intro a
    rcases le_total (q a).toReal (p a).toReal with h | h
    · rw [max_eq_left (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]; ring
    · rw [max_eq_right (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring
  have h1 : ∑' a, ((p a).toReal - (q a).toReal) = 0 := by
    rw [(pmf_summable_toReal p).tsum_sub (pmf_summable_toReal q), pmf_tsum_toReal,
      pmf_tsum_toReal, sub_self]
  rw [tsum_congr hdiff, hpos.tsum_sub hneg] at h1
  unfold pmfTV
  rw [tsum_congr habs, hpos.tsum_add hneg]
  linarith

theorem tsum_tsub_bind_le (p q : PMF α) (f : α → PMF β) :
    ∑' b, (p.bind f b - q.bind f b) ≤ ∑' a, (p a - q a) := by
  calc ∑' b, (p.bind f b - q.bind f b) ≤ ∑' b, ∑' a, (p a - q a) * f a b := by
        refine ENNReal.tsum_le_tsum fun b => ?_
        rw [PMF.bind_apply, PMF.bind_apply, tsub_le_iff_right, ← ENNReal.tsum_add]
        exact ENNReal.tsum_le_tsum fun a => by rw [← add_mul]; gcongr; exact le_tsub_add
    _ = ∑' a, (p a - q a) := by
        rw [ENNReal.tsum_comm]
        congr 1; funext a
        rw [ENNReal.tsum_mul_left, (f a).tsum_coe, mul_one]

/-- Data processing: a common Markov kernel does not increase total variation. -/
theorem pmfTV_bind_le (p q : PMF α) (f : α → PMF β) :
    pmfTV (p.bind f) (q.bind f) ≤ pmfTV p q := by
  rw [pmfTV_eq_toReal_tsum_tsub, pmfTV_eq_toReal_tsum_tsub]
  exact ENNReal.toReal_mono (tsum_tsub_ne_top p q) (tsum_tsub_bind_le p q f)

theorem pmfTV_map_le (p q : PMF α) (f : α → β) : pmfTV (p.map f) (q.map f) ≤ pmfTV p q := by
  simpa only [PMF.bind_pure_comp] using pmfTV_bind_le p q (PMF.pure ∘ f)

end TV

section Mixture

variable {ι α β : Type*} [Fintype ι] [Nonempty ι]

/-- The law of the observation when the root state is uniform on `ι`. -/
def pmfMixture (law : ι → PMF α) : PMF α := (PMF.uniformOfFintype ι).bind law

theorem pmfMixture_apply (law : ι → PMF α) (a : α) :
    pmfMixture law a = (Fintype.card ι : ℝ≥0∞)⁻¹ * ∑ i, law i a := by
  simp [pmfMixture, PMF.bind_apply, PMF.uniformOfFintype_apply, tsum_fintype, Finset.mul_sum]

theorem toReal_pmfMixture_apply (law : ι → PMF α) (a : α) :
    (pmfMixture law a).toReal = (∑ i, (law i a).toReal) / Fintype.card ι := by
  rw [pmfMixture_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum (fun i _ => (law i).apply_ne_top a)]
  ring

/-- Any PMF on `ι` with all weights `(card ι)⁻¹` mixes to `pmfMixture`. -/
theorem bind_eq_pmfMixture (μ : PMF ι) (hμ : ∀ i, μ i = (Fintype.card ι : ℝ≥0∞)⁻¹)
    (law : ι → PMF α) : μ.bind law = pmfMixture law := by
  congr 1; exact PMF.ext fun i => by rw [hμ, PMF.uniformOfFintype_apply]

theorem pmfMixture_eq_zero_iff (law : ι → PMF α) (a : α) :
    pmfMixture law a = 0 ↔ ∀ i, law i a = 0 := by
  simp [pmfMixture_apply, Finset.sum_eq_zero_iff]

theorem pmfMixture_bind (law : ι → PMF α) (f : α → PMF β) :
    pmfMixture (fun i => (law i).bind f) = (pmfMixture law).bind f :=
  (PMF.bind_bind _ _ _).symm

/-- Reconstruction advantage of the family `law` (root state uniform on `ι`): the average over
`i` of the total variation distance between `law i` and the mixture. -/
def reconAdvantage (law : ι → PMF α) : ℝ :=
  (∑ i, pmfTV (law i) (pmfMixture law)) / Fintype.card ι

theorem reconAdvantage_nonneg (law : ι → PMF α) : 0 ≤ reconAdvantage law :=
  div_nonneg (Finset.sum_nonneg fun _ _ => pmfTV_nonneg _ _) (Nat.cast_nonneg _)

theorem reconAdvantage_le_one (law : ι → PMF α) : reconAdvantage law ≤ 1 := by
  have hk : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  rw [reconAdvantage, div_le_one hk]
  calc ∑ i, pmfTV (law i) (pmfMixture law) ≤ ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => pmfTV_le_one _ _
    _ = Fintype.card ι := by simp

/-- Data processing for the reconstruction advantage. -/
theorem reconAdvantage_bind_le (law : ι → PMF α) (f : α → PMF β) :
    reconAdvantage (fun i => (law i).bind f) ≤ reconAdvantage law := by
  unfold reconAdvantage
  rw [pmfMixture_bind]
  gcongr with i
  exact pmfTV_bind_le _ _ f

theorem reconAdvantage_map_le (law : ι → PMF α) (f : α → β) :
    reconAdvantage (fun i => (law i).map f) ≤ reconAdvantage law := by
  simpa only [PMF.bind_pure_comp] using reconAdvantage_bind_le law (PMF.pure ∘ f)

/-- Observing the state itself: `reconAdvantage (fun i => pure (leaf i)) = 1 - 1 / card ι` for
injective `leaf`. -/
theorem reconAdvantage_pure {γ : Type*} {leaf : ι → γ} (hleaf : Function.Injective leaf) :
    reconAdvantage (fun i => PMF.pure (leaf i)) = 1 - 1 / Fintype.card ι := by
  classical
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hmix : ∀ i, pmfMixture (fun i => PMF.pure (leaf i)) (leaf i) =
      (Fintype.card ι : ℝ≥0∞)⁻¹ := by
    intro i
    rw [pmfMixture_apply]
    simp [PMF.pure_apply, hleaf.eq_iff]
  have htv : ∀ i, pmfTV (PMF.pure (leaf i)) (pmfMixture fun i => PMF.pure (leaf i)) =
      1 - 1 / Fintype.card ι := by
    intro i
    rw [pmfTV_eq_toReal_tsum_tsub, tsum_eq_single (leaf i) fun b hb => by
      simp [PMF.pure_apply, hb]]
    rw [PMF.pure_apply_self, hmix, ENNReal.toReal_sub_of_le
      (ENNReal.inv_le_one.2 (by exact_mod_cast Fintype.card_pos)) ENNReal.one_ne_top]
    simp
  rw [reconAdvantage, Finset.sum_congr rfl fun i _ => htv i]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Two root states that are distinguishable give a positive advantage. -/
theorem pmfTV_le_card_mul_reconAdvantage (law : ι → PMF α) (i j : ι) :
    pmfTV (law i) (law j) ≤ Fintype.card ι * reconAdvantage law := by
  classical
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [reconAdvantage, mul_div_cancel₀ _ hk]
  by_cases hij : i = j
  · subst hij; simpa using Finset.sum_nonneg fun k _ => pmfTV_nonneg (law k) (pmfMixture law)
  calc pmfTV (law i) (law j) ≤ pmfTV (law i) (pmfMixture law) + pmfTV (law j) (pmfMixture law) := by
        rw [pmfTV_comm (law j)]; exact pmfTV_triangle _ _ _
    _ = ∑ k ∈ {i, j}, pmfTV (law k) (pmfMixture law) := by rw [Finset.sum_pair hij]
    _ ≤ ∑ k, pmfTV (law k) (pmfMixture law) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ => pmfTV_nonneg _ _

end Mixture

section Posterior

variable {ι α : Type*} [Fintype ι] [Nonempty ι]

/-- Posterior form of the reconstruction advantage. If `post y i` is any posterior with
`(pmfMixture law y).toReal * post y i = c * (law i y).toReal` and `card ι * c = 1`, then
`∑' y, m(y) · (∑ i, |post y i - c|) / 2` is `reconAdvantage law`. -/
theorem tsum_mul_posterior_eq_reconAdvantage (law : ι → PMF α) (c : ℝ)
    (hc : (Fintype.card ι : ℝ) * c = 1) (post : α → ι → ℝ)
    (hpost : ∀ y i, (pmfMixture law y).toReal * post y i = c * (law i y).toReal) :
    ∑' y, (pmfMixture law y).toReal * ((∑ i, |post y i - c|) / 2) = reconAdvantage law := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc0 : 0 ≤ c :=
    (pos_of_mul_pos_right (hc ▸ one_pos) (Nat.cast_nonneg (Fintype.card ι))).le
  have hm : ∀ y, (pmfMixture law y).toReal = c * ∑ i, (law i y).toReal := by
    intro y
    rw [toReal_pmfMixture_apply, div_eq_iff hk]
    linear_combination -(∑ i, (law i y).toReal) * hc
  have hterm : ∀ y i, (pmfMixture law y).toReal * |post y i - c| =
      c * |(law i y).toReal - (pmfMixture law y).toReal| := by
    intro y i
    rw [← abs_of_nonneg (ENNReal.toReal_nonneg (a := pmfMixture law y)), ← abs_mul,
      ← abs_of_nonneg hc0, ← abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg hc0]
    congr 1
    rw [mul_sub, hpost, mul_sub, hm]
    ring
  have hsum : ∀ i, Summable fun y => |(law i y).toReal - (pmfMixture law y).toReal| :=
    fun i => pmf_summable_abs_sub _ _
  calc ∑' y, (pmfMixture law y).toReal * ((∑ i, |post y i - c|) / 2)
      = ∑' y, ∑ i, c / 2 * |(law i y).toReal - (pmfMixture law y).toReal| := by
        congr 1; funext y
        rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
        congr 1; funext i
        rw [hterm]; ring
    _ = ∑ i, c / 2 * ∑' y, |(law i y).toReal - (pmfMixture law y).toReal| := by
        rw [Summable.tsum_finsetSum fun i _ => (hsum i).mul_left _]
        congr 1; funext i
        rw [tsum_mul_left]
    _ = reconAdvantage law := by
        rw [reconAdvantage, eq_div_iff hk, Finset.sum_mul]
        congr 1; funext i
        rw [pmfTV]
        linear_combination (∑' y, |(law i y).toReal - (pmfMixture law y).toReal|) / 2 * hc

/-- The posterior `if m y = 0 then c else (law i y).toReal / (card ι * (m y).toReal)`. -/
theorem tsum_mul_posterior_ite_eq_reconAdvantage (law : ι → PMF α) (c : ℝ)
    (hc : (Fintype.card ι : ℝ) * c = 1) :
    ∑' y, (pmfMixture law y).toReal * ((∑ i, |(if pmfMixture law y = 0 then c else
      (law i y).toReal / ((Fintype.card ι : ℝ) * (pmfMixture law y).toReal)) - c|) / 2) =
      reconAdvantage law := by
  refine tsum_mul_posterior_eq_reconAdvantage law c hc _ fun y i => ?_
  split_ifs with h
  · rw [(pmfMixture_eq_zero_iff law y).1 h i, h]; simp
  · have hm : (pmfMixture law y).toReal ≠ 0 :=
      (ENNReal.toReal_pos h ((pmfMixture law).apply_ne_top y)).ne'
    have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp
    linear_combination -(law i y).toReal * hc

theorem toReal_mul_toReal_div_of_le {x y : ℝ≥0∞} (hy : y ≠ ∞) (hxy : x ≤ y) :
    y.toReal * (x / y).toReal = x.toReal := by
  rcases eq_or_ne y 0 with rfl | h0
  · simp [nonpos_iff_eq_zero.1 hxy]
  · rw [← ENNReal.toReal_mul, ENNReal.mul_div_cancel h0 hy]

/-- The posterior `((c * law i y) / ∑ j, c * law j y).toReal` in `ℝ≥0∞` with
`c = (card ι)⁻¹`. -/
theorem tsum_mul_posterior_div_eq_reconAdvantage (law : ι → PMF α) :
    ∑' y, (∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * law j y).toReal *
      ((∑ i, |((Fintype.card ι : ℝ≥0∞)⁻¹ * law i y / ∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * law j y
        ).toReal - (Fintype.card ι : ℝ)⁻¹|) / 2) = reconAdvantage law := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hmix : ∀ y, ∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * law j y = pmfMixture law y := by
    intro y; rw [pmfMixture_apply, Finset.mul_sum]
  simp only [hmix]
  refine tsum_mul_posterior_eq_reconAdvantage law _ (mul_inv_cancel₀ hk) _ fun y i => ?_
  rw [toReal_mul_toReal_div_of_le ((pmfMixture law).apply_ne_top y), ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [pmfMixture_apply]
  calc (Fintype.card ι : ℝ≥0∞)⁻¹ * law i y = ∑ j ∈ {i}, (Fintype.card ι : ℝ≥0∞)⁻¹ * law j y := by
        simp
    _ ≤ ∑ j, (Fintype.card ι : ℝ≥0∞)⁻¹ * law j y :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := by rw [Finset.mul_sum]

end Posterior

section Limit

/-- An antitone sequence bounded below by `0` converges to its infimum. -/
theorem tendsto_iInf_of_antitone_nonneg {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ n, 0 ≤ a n) :
    Tendsto a atTop (nhds (⨅ n, a n)) :=
  tendsto_atTop_ciInf ha ⟨0, by rintro _ ⟨n, rfl⟩; exact h0 n⟩

/-- For an antitone sequence bounded below by `0`, a positive limit exists exactly when the
sequence is bounded below by a positive constant. -/
theorem exists_pos_tendsto_iff_of_antitone {a : ℕ → ℝ} (ha : Antitone a) (h0 : ∀ n, 0 ≤ a n) :
    (∃ L, 0 < L ∧ Tendsto a atTop (nhds L)) ↔ ∃ ε, 0 < ε ∧ ∀ n, ε ≤ a n := by
  constructor
  · rintro ⟨L, hL, hlim⟩
    exact ⟨L, hL, fun n => ha.le_of_tendsto hlim n⟩
  · rintro ⟨ε, hε, hle⟩
    refine ⟨⨅ n, a n, hε.trans_le (le_ciInf hle), tendsto_iInf_of_antitone_nonneg ha h0⟩

/-- The same with the lower bound required only eventually. -/
theorem exists_pos_tendsto_iff_eventually_of_antitone {a : ℕ → ℝ} (ha : Antitone a)
    (h0 : ∀ n, 0 ≤ a n) :
    (∃ L, 0 < L ∧ Tendsto a atTop (nhds L)) ↔ ∃ ε, 0 < ε ∧ ∀ᶠ n in atTop, ε ≤ a n := by
  rw [exists_pos_tendsto_iff_of_antitone ha h0]
  refine ⟨fun ⟨ε, hε, h⟩ => ⟨ε, hε, Eventually.of_forall h⟩, fun ⟨ε, hε, h⟩ => ⟨ε, hε, ?_⟩⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact fun n => (hN (max n N) (le_max_right _ _)).trans (ha (le_max_left _ _))

end Limit

section Traverse

variable {α β : Type*}

/-- `iidList p k`: `k` independent draws from `p`, as a list. -/
def iidList (p : PMF α) : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | k + 1 => p.bind fun a => (iidList p k).map (List.cons a)

/-- Every function with the defining equations of `iidList` is `iidList` (bridge to local copies
of the definition: `iidList_eq_of_rec Local.iidList (fun _ => rfl) (fun _ _ => rfl)`). -/
theorem iidList_eq_of_rec (f : PMF α → ℕ → PMF (List α)) (h0 : ∀ p, f p 0 = PMF.pure [])
    (hs : ∀ p k, f p (k + 1) = p.bind fun a => (f p k).map (List.cons a)) : iidList = f := by
  funext p k
  induction k with
  | zero => exact (h0 p).symm
  | succ k ih => rw [hs, ← ih]; rfl

/-- Apply the kernel `g` independently to every entry of a list. -/
def listTraverse (g : α → PMF β) : List α → PMF (List β)
  | [] => PMF.pure []
  | a :: l => (g a).bind fun b => (listTraverse g l).map (List.cons b)

theorem listTraverse_perm (g : α → PMF β) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    (listTraverse g l₁).map (fun l : List β => (l : Multiset β)) =
      (listTraverse g l₂).map (fun l : List β => (l : Multiset β)) := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    simp only [listTraverse, PMF.map_bind, PMF.map_comp]
    congr 1
    funext b
    have := congrArg (PMF.map (Multiset.cons b)) ih
    simp only [PMF.map_comp] at this
    exact this
  | swap a b l =>
    simp only [listTraverse, PMF.map_bind, PMF.map_comp]
    rw [PMF.bind_comm]
    congr 1; funext x; congr 1; funext y
    congr 1; funext l
    simpa [Function.comp] using List.Perm.swap x y l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Apply the kernel `g` independently to every element of a multiset. -/
def multisetTraverse (g : α → PMF β) (s : Multiset α) : PMF (Multiset β) :=
  Quotient.liftOn s (fun l => (listTraverse g l).map (fun l : List β => (l : Multiset β)))
    fun _ _ h => listTraverse_perm g h

theorem multisetTraverse_coe (g : α → PMF β) (l : List α) :
    multisetTraverse g (l : Multiset α) =
      (listTraverse g l).map (fun l : List β => (l : Multiset β)) := rfl

/-- Independent draws from `p.bind g`: draw from `p`, then apply `g` entrywise. -/
theorem iidList_bind (p : PMF α) (g : α → PMF β) (k : ℕ) :
    iidList (p.bind g) k = (iidList p k).bind (listTraverse g) := by
  induction k with
  | zero => simp [iidList, listTraverse]
  | succ k ih =>
    simp only [iidList, ih, PMF.bind_bind, PMF.bind_map]
    congr 1; funext a
    simp only [PMF.map_bind, Function.comp_def, listTraverse]
    rw [PMF.bind_comm]

theorem iidList_multiset_bind (p : PMF α) (g : α → PMF β) (k : ℕ) :
    (iidList (p.bind g) k).map (fun l : List β => (l : Multiset β)) =
      ((iidList p k).map (fun l : List α => (l : Multiset α))).bind (multisetTraverse g) := by
  rw [iidList_bind, PMF.map_bind, PMF.bind_map]
  rfl

/-- The coercion `List → Multiset` written with an untyped binder elaborates to
`PMF.map (fun s => s) (p >>= fun l => pure ↑l)`; this is `p.map (↑)`. -/
theorem map_id_bind_pure_coe (p : PMF (List α)) :
    PMF.map (fun s : Multiset α => s) (p >>= fun l => pure (l : Multiset α)) =
      p.map (fun l : List α => (l : Multiset α)) :=
  PMF.map_id _

theorem length_eq_of_mem_support_iidList (p : PMF α) {k : ℕ} {l : List α}
    (hl : l ∈ (iidList p k).support) : l.length = k := by
  induction k generalizing l with
  | zero => simpa [iidList] using hl
  | succ k ih =>
    simp only [iidList, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hl
    obtain ⟨a, -, l', hl', rfl⟩ := hl
    simp [ih hl']

end Traverse

section Tower

variable {ι : Type*} {O : ℕ → Type*}

/-- `law` is the law of the depth-`n` observation of a branching broadcast: offspring numbers
drawn from `N`, each child's state drawn from `K` of its parent's state, and the depth-`n`
observation of the tree below a vertex of state `i` is `law n i`. The observation types form a
tower: depth `0` observes the state through `leaf`, depth `n + 1` observes the multiset of the
children's depth-`n` observations through `up n` (both the identity in the usual formalizations,
where `O (n + 1)` unfolds to `Multiset (O n)`). -/
structure IsBroadcastLaw (K : ι → PMF ι) (N : PMF ℕ) (leaf : ι → O 0)
    (up : ∀ n, Multiset (O n) → O (n + 1)) (law : (n : ℕ) → ι → PMF (O n)) : Prop where
  zero : ∀ i, law 0 i = PMF.pure (leaf i)
  succ : ∀ n i, law (n + 1) i = N.bind fun k =>
    (iidList ((K i).bind (law n)) k).map fun xs : List (O n) => up n (xs : Multiset (O n))

/-- The kernel that grows a depth-`n` observation into a depth-`n + 1` one: extend every leaf
by an independent subtree. -/
def towerGrow (root : O 0 → ι) (up : ∀ n, Multiset (O n) → O (n + 1))
    (down : ∀ n, O (n + 1) → Multiset (O n)) (law₁ : ι → PMF (O 1)) :
    (n : ℕ) → O n → PMF (O (n + 1))
  | 0, x => law₁ (root x)
  | n + 1, s => (multisetTraverse (towerGrow root up down law₁ n) (down n s)).map (up (n + 1))

/-- The depth-`n + 1` observation is a randomized function of the depth-`n` one. -/
theorem IsBroadcastLaw.succ_eq_bind {K : ι → PMF ι} {N : PMF ℕ} {leaf : ι → O 0}
    {up : ∀ n, Multiset (O n) → O (n + 1)} {law : (n : ℕ) → ι → PMF (O n)}
    (h : IsBroadcastLaw K N leaf up law) (root : O 0 → ι) (hroot : ∀ i, root (leaf i) = i)
    (down : ∀ n, O (n + 1) → Multiset (O n)) (hdown : ∀ n s, down n (up n s) = s) (n : ℕ)
    (i : ι) : law (n + 1) i = (law n i).bind (towerGrow root up down (law 1) n) := by
  induction n generalizing i with
  | zero => rw [h.zero, PMF.pure_bind, towerGrow, hroot]
  | succ n ih =>
    have hq : (K i).bind (law (n + 1)) =
        ((K i).bind (law n)).bind (towerGrow root up down (law 1) n) := by
      rw [PMF.bind_bind]; congr 1; funext j; exact ih j
    rw [h.succ (n + 1) i, hq, h.succ n i, PMF.bind_bind N]
    congr 1; funext k
    rw [iidList_bind, PMF.map_bind, PMF.bind_map]
    congr 1; funext l
    simp only [Function.comp_apply, towerGrow, hdown, multisetTraverse_coe, PMF.map_comp]
    rfl

/-- Laws related by a kernel at every depth have antitone reconstruction advantage. -/
theorem reconAdvantage_antitone_of_succ [Fintype ι] [Nonempty ι]
    (law : (n : ℕ) → ι → PMF (O n)) (grow : (n : ℕ) → O n → PMF (O (n + 1)))
    (h : ∀ n i, law (n + 1) i = (law n i).bind (grow n)) :
    Antitone fun n => reconAdvantage (law n) :=
  antitone_nat_of_succ_le fun n => by
    rw [show law (n + 1) = fun i => (law n i).bind (grow n) from funext (h n)]
    exact reconAdvantage_bind_le _ _

variable [Fintype ι] [Nonempty ι] {K : ι → PMF ι} {N : PMF ℕ} {leaf : ι → O 0}
  {up : ∀ n, Multiset (O n) → O (n + 1)} {law : (n : ℕ) → ι → PMF (O n)}

theorem IsBroadcastLaw.antitone (h : IsBroadcastLaw K N leaf up law)
    (hleaf : Function.Injective leaf) (hup : ∀ n, Function.Injective (up n)) :
    Antitone fun n => reconAdvantage (law n) :=
  reconAdvantage_antitone_of_succ law _ (h.succ_eq_bind (Function.invFun leaf)
    (Function.leftInverse_invFun hleaf) (fun n => Function.invFun (up n))
    (fun n => Function.leftInverse_invFun (hup n)))

/-- The reconstruction advantage of a broadcast converges, to its infimum over depths. -/
theorem IsBroadcastLaw.tendsto (h : IsBroadcastLaw K N leaf up law)
    (hleaf : Function.Injective leaf) (hup : ∀ n, Function.Injective (up n)) :
    Tendsto (fun n => reconAdvantage (law n)) atTop (nhds (⨅ n, reconAdvantage (law n))) :=
  tendsto_iInf_of_antitone_nonneg (h.antitone hleaf hup) fun _ => reconAdvantage_nonneg _

/-- Reconstruction in the sense "positive limit" is a uniform lower bound over depths. -/
theorem IsBroadcastLaw.exists_pos_tendsto_iff (h : IsBroadcastLaw K N leaf up law)
    (hleaf : Function.Injective leaf) (hup : ∀ n, Function.Injective (up n)) :
    (∃ L, 0 < L ∧ Tendsto (fun n => reconAdvantage (law n)) atTop (nhds L)) ↔
      ∃ ε, 0 < ε ∧ ∀ n, ε ≤ reconAdvantage (law n) :=
  exists_pos_tendsto_iff_of_antitone (h.antitone hleaf hup) fun _ => reconAdvantage_nonneg _

end Tower

section TreeModel

variable {ι : Type*}

/-- Observation tower of a rooted tree with states in `ι`: depth `0` sees a state, depth `n + 1`
the multiset of the children's depth-`n` observations. -/
def TreeObs (ι : Type*) : ℕ → Type _
  | 0 => ι
  | n + 1 => Multiset (TreeObs ι n)

/-- Law of the depth-`n` leaf observation of a Galton–Watson broadcast with offspring law `N` and
channel `K`, root state `i`. -/
def treeLaw (K : ι → PMF ι) (N : PMF ℕ) : (n : ℕ) → ι → PMF (TreeObs ι n)
  | 0, i => PMF.pure i
  | n + 1, i => N.bind fun k =>
      (iidList ((K i).bind (treeLaw K N n)) k).map
        (fun xs : List (TreeObs ι n) => (xs : Multiset (TreeObs ι n)))

theorem isBroadcastLaw_treeLaw (K : ι → PMF ι) (N : PMF ℕ) :
    IsBroadcastLaw (O := TreeObs ι) K N (fun i => i) (fun _ s => s) (treeLaw K N) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem reconAdvantage_treeLaw_antitone [Fintype ι] [Nonempty ι] (K : ι → PMF ι) (N : PMF ℕ) :
    Antitone fun n => reconAdvantage (treeLaw K N n) :=
  (isBroadcastLaw_treeLaw K N).antitone (fun _ _ h => h) fun _ _ _ h => h

end TreeModel

section Potts

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Symmetric (Potts) channel on `ι` with eigenvalue `lam`: keep the state with probability
`lam`, otherwise resample uniformly. Diagonal `(1 + (k - 1) lam) / k`, off-diagonal
`(1 - lam) / k`, `k = card ι`. -/
def pottsWeight (lam : ℝ) (i j : ι) : ℝ :=
  if i = j then (1 + ((Fintype.card ι : ℝ) - 1) * lam) / Fintype.card ι
  else (1 - lam) / Fintype.card ι

theorem pottsWeight_eq [Nonempty ι] (lam : ℝ) (i j : ι) :
    pottsWeight lam i j = lam * (if i = j then 1 else 0) + (1 - lam) / Fintype.card ι := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold pottsWeight; split_ifs <;> field_simp <;> ring

theorem sum_pottsWeight [Nonempty ι] (lam : ℝ) (i : ι) : ∑ j, pottsWeight lam i j = 1 := by
  have hk : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [pottsWeight_eq, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp; ring

theorem pottsWeight_nonneg {lam : ℝ} (h₁ : -1 ≤ ((Fintype.card ι : ℝ) - 1) * lam)
    (h₂ : lam ≤ 1) (i j : ι) : 0 ≤ pottsWeight lam i j := by
  unfold pottsWeight
  split_ifs
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- Action on functions: `∑ j, W i j f j = lam f i + (1 - lam) · mean f`. -/
theorem sum_pottsWeight_mul [Nonempty ι] (lam : ℝ) (f : ι → ℝ) (i : ι) :
    ∑ j, pottsWeight lam i j * f j = lam * f i + (1 - lam) * ((∑ j, f j) / Fintype.card ι) := by
  simp only [pottsWeight_eq, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

/-- Centred functions are eigenfunctions with eigenvalue `lam`. -/
theorem sum_pottsWeight_mul_of_sum_eq_zero [Nonempty ι] (lam : ℝ) {f : ι → ℝ}
    (hf : ∑ j, f j = 0) (i : ι) : ∑ j, pottsWeight lam i j * f j = lam * f i := by
  rw [sum_pottsWeight_mul, hf]; ring

/-- Two steps of the channel are one step with eigenvalue `lam * mu`. -/
theorem sum_pottsWeight_mul_pottsWeight [Nonempty ι] (lam mu : ℝ) (i k : ι) :
    ∑ j, pottsWeight lam i j * pottsWeight mu j k = pottsWeight (lam * mu) i k := by
  rw [sum_pottsWeight_mul, show ∑ j, pottsWeight mu j k = 1 by
    simpa [pottsWeight, eq_comm] using sum_pottsWeight mu k]
  simp only [pottsWeight_eq]
  ring

theorem pottsWeight_fin_three (lam : ℝ) (i j : Fin 3) :
    pottsWeight lam i j = if i = j then (1 + 2 * lam) / 3 else (1 - lam) / 3 := by
  simp only [pottsWeight, Fintype.card_fin]; norm_num

/-- The Potts channel as a Markov kernel. -/
def pottsPMF [Nonempty ι] {lam : ℝ} (h₁ : -1 ≤ ((Fintype.card ι : ℝ) - 1) * lam) (h₂ : lam ≤ 1)
    (i : ι) : PMF ι :=
  PMF.ofFintype (fun j => ENNReal.ofReal (pottsWeight lam i j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => pottsWeight_nonneg h₁ h₂ i j,
      sum_pottsWeight, ENNReal.ofReal_one])

theorem toReal_pottsPMF_apply [Nonempty ι] {lam : ℝ} (h₁ : -1 ≤ ((Fintype.card ι : ℝ) - 1) * lam)
    (h₂ : lam ≤ 1) (i j : ι) : (pottsPMF h₁ h₂ i j).toReal = pottsWeight lam i j := by
  simp [pottsPMF, ENNReal.toReal_ofReal (pottsWeight_nonneg h₁ h₂ i j)]

end Potts

section Distinguisher

variable {α : Type*}

/-- Second-moment distinguisher: for a statistic `S` with finite second moments,
`(E_p S - E_q S)^2 ≤ 2 tv(p, q) (E_p S^2 + E_q S^2)`. -/
theorem sq_sub_le_pmfTV_mul (p q : PMF α) (S : α → ℝ)
    (hp : Summable fun a => (p a).toReal * S a ^ 2)
    (hq : Summable fun a => (q a).toReal * S a ^ 2) :
    (∑' a, (p a).toReal * S a - ∑' a, (q a).toReal * S a) ^ 2 ≤
      2 * pmfTV p q * (∑' a, (p a).toReal * S a ^ 2 + ∑' a, (q a).toReal * S a ^ 2) := by
  set u : α → ℝ := fun a => |(p a).toReal - (q a).toReal|
  have hu : Summable u := pmf_summable_abs_sub p q
  have hP := pmf_summable_toReal p
  have hQ := pmf_summable_toReal q
  have hbound : ∀ a, |S a| ≤ 1 + S a ^ 2 := fun a => by nlinarith [abs_nonneg (S a), sq_abs (S a)]
  have hpS : Summable fun a => (p a).toReal * S a :=
    Summable.of_norm_bounded (hP.add hp) fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      nlinarith [hbound a, ENNReal.toReal_nonneg (a := p a)]
  have hqS : Summable fun a => (q a).toReal * S a :=
    Summable.of_norm_bounded (hQ.add hq) fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      nlinarith [hbound a, ENNReal.toReal_nonneg (a := q a)]
  have huS2 : Summable fun a => u a * S a ^ 2 :=
    Summable.of_nonneg_of_le (fun a => mul_nonneg (abs_nonneg _) (sq_nonneg _))
      (fun a => by
        have : u a ≤ (p a).toReal + (q a).toReal := (abs_sub _ _).trans (by
          rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg])
        nlinarith [sq_nonneg (S a)]) (hp.add hq)
  have huS2_le : ∑' a, u a * S a ^ 2 ≤
      ∑' a, (p a).toReal * S a ^ 2 + ∑' a, (q a).toReal * S a ^ 2 := by
    rw [← hp.tsum_add hq]
    exact huS2.tsum_le_tsum (fun a => by
      have : u a ≤ (p a).toReal + (q a).toReal := (abs_sub _ _).trans (by
        rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg])
      nlinarith [sq_nonneg (S a)]) (hp.add hq)
  set g := ∑' a, (p a).toReal * S a - ∑' a, (q a).toReal * S a
  set T := ∑' a, u a
  set M := ∑' a, u a * S a ^ 2
  have hT : T = 2 * pmfTV p q := by simp only [T, u, pmfTV]; ring
  have hM0 : 0 ≤ M := tsum_nonneg fun a => mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hT0 : 0 ≤ T := tsum_nonneg fun a => abs_nonneg _
  -- `2 t |g| ≤ t^2 M + T` for all `t`.
  have key : ∀ t : ℝ, 0 ≤ t → 2 * t * |g| ≤ t ^ 2 * M + T := by
    intro t ht
    have hg : g = ∑' a, ((p a).toReal - (q a).toReal) * S a := by
      simp only [g]; rw [← hpS.tsum_sub hqS]; congr 1; funext a; ring
    have hsum : Summable fun a => ((p a).toReal - (q a).toReal) * S a := by
      simpa only [sub_mul] using hpS.sub hqS
    have habs : |g| ≤ ∑' a, u a * |S a| := by
      rw [hg]
      refine (norm_tsum_le_tsum_norm hsum.norm).trans_eq ?_
      congr 1; funext a; rw [Real.norm_eq_abs, abs_mul]
    have huS : Summable fun a => u a * |S a| :=
      Summable.of_nonneg_of_le (fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (fun a => by nlinarith [hbound a, abs_nonneg ((p a).toReal - (q a).toReal)])
        (hu.add huS2)
    calc 2 * t * |g| ≤ 2 * t * ∑' a, u a * |S a| := by gcongr
      _ = ∑' a, 2 * t * (u a * |S a|) := by rw [tsum_mul_left]
      _ ≤ ∑' a, (t ^ 2 * (u a * S a ^ 2) + u a) :=
          (huS.mul_left _).tsum_le_tsum (fun a => by
            have h0 : 0 ≤ u a * (t * |S a| - 1) ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
            rw [← sq_abs (S a)]
            linear_combination h0) ((huS2.mul_left _).add hu)
      _ = t ^ 2 * M + T := by rw [(huS2.mul_left _).tsum_add hu, tsum_mul_left]
  rw [← hT]
  have hgoal : g ^ 2 ≤ T * M := by
    rcases hM0.eq_or_lt with hM | hM
    · have : g = 0 := by
        by_contra hg
        have hgpos : 0 < |g| := abs_pos.2 hg
        have h1 := key ((T + 1) / |g|) (by positivity)
        have h2 : 2 * ((T + 1) / |g|) * |g| = 2 * (T + 1) := by field_simp
        rw [h2, ← hM, mul_zero, zero_add] at h1
        linarith
      rw [this, ← hM]; simp
    · have := key (|g| / M) (by positivity)
      have h2 : 2 * (|g| / M) * |g| = 2 * (|g| ^ 2 / M) := by ring
      have h3 : (|g| / M) ^ 2 * M = |g| ^ 2 / M := by field_simp
      rw [h2, h3] at this
      have : |g| ^ 2 / M ≤ T := by linarith
      rw [div_le_iff₀ hM] at this
      nlinarith [sq_abs g]
  calc g ^ 2 ≤ T * M := hgoal
    _ ≤ T * (∑' a, (p a).toReal * S a ^ 2 + ∑' a, (q a).toReal * S a ^ 2) := by gcongr

/-- Centred form: the shift `c` is free, `(E_p S - E_q S)^2 ≤ 2 tv(p, q) (E_p (S - c)^2 +
E_q (S - c)^2)`. -/
theorem sq_sub_le_pmfTV_mul_centred (p q : PMF α) (S : α → ℝ) (c : ℝ)
    (hp : Summable fun a => (p a).toReal * S a ^ 2)
    (hq : Summable fun a => (q a).toReal * S a ^ 2) :
    (∑' a, (p a).toReal * S a - ∑' a, (q a).toReal * S a) ^ 2 ≤
      2 * pmfTV p q * (∑' a, (p a).toReal * (S a - c) ^ 2 +
        ∑' a, (q a).toReal * (S a - c) ^ 2) := by
  have hsq : ∀ (r : PMF α), Summable (fun a => (r a).toReal * S a ^ 2) →
      Summable fun a => (r a).toReal * (S a - c) ^ 2 := fun r hr =>
    Summable.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
      (fun a => by
        have := ENNReal.toReal_nonneg (a := r a)
        nlinarith [sq_nonneg (S a + c)])
      ((hr.mul_left 2).add ((pmf_summable_toReal r).mul_right (2 * c ^ 2)))
  have hlin : ∀ (r : PMF α), Summable (fun a => (r a).toReal * S a ^ 2) →
      ∑' a, (r a).toReal * (S a - c) = ∑' a, (r a).toReal * S a - c := fun r hr => by
    have hS : Summable fun a => (r a).toReal * S a :=
      Summable.of_norm_bounded ((pmf_summable_toReal r).add hr) fun a => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        nlinarith [abs_nonneg (S a), sq_abs (S a), ENNReal.toReal_nonneg (a := r a),
          sq_nonneg (|S a| - 1)]
    simp only [mul_sub]
    rw [hS.tsum_sub ((pmf_summable_toReal r).mul_right c), tsum_mul_right, pmf_tsum_toReal,
      one_mul]
  have := sq_sub_le_pmfTV_mul p q (fun a => S a - c) (hsq p hp) (hsq q hq)
  rwa [hlin p hp, hlin q hq, sub_sub_sub_cancel_right] at this

/-- `E_p (S - c)^2 = E_p S^2 - 2 c E_p S + c^2`. -/
theorem tsum_mul_sub_sq (p : PMF α) (S : α → ℝ) (c : ℝ)
    (hp : Summable fun a => (p a).toReal * S a ^ 2) :
    ∑' a, (p a).toReal * (S a - c) ^ 2 =
      ∑' a, (p a).toReal * S a ^ 2 - 2 * c * ∑' a, (p a).toReal * S a + c ^ 2 := by
  have hS : Summable fun a => (p a).toReal * S a :=
    Summable.of_norm_bounded ((pmf_summable_toReal p).add hp) fun a => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      nlinarith [abs_nonneg (S a), sq_abs (S a), ENNReal.toReal_nonneg (a := p a),
        sq_nonneg (|S a| - 1)]
  have h : ∀ a, (p a).toReal * (S a - c) ^ 2 =
      (p a).toReal * S a ^ 2 - 2 * c * ((p a).toReal * S a) + (p a).toReal * c ^ 2 :=
    fun a => by ring
  rw [tsum_congr h, (hp.sub (hS.mul_left _)).tsum_add ((pmf_summable_toReal p).mul_right _),
    hp.tsum_sub (hS.mul_left _), tsum_mul_left, tsum_mul_right, pmf_tsum_toReal, one_mul]

end Distinguisher

section Wald

variable {α β : Type*}

theorem tsum_pure_mul (a : α) (F : α → ℝ≥0∞) : ∑' b, PMF.pure a b * F b = F a := by
  rw [tsum_eq_single a fun b hb => by simp [PMF.pure_apply, hb]]
  simp

/-- Tower rule in `ℝ≥0∞`: `E_{p.bind f} F = E_p (a ↦ E_{f a} F)`. -/
theorem tsum_bind_mul (p : PMF α) (f : α → PMF β) (F : β → ℝ≥0∞) :
    ∑' b, p.bind f b * F b = ∑' a, p a * ∑' b, f a b * F b := by
  calc ∑' b, p.bind f b * F b = ∑' b, ∑' a, p a * (f a b * F b) := by
        congr 1; funext b
        rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
        congr 1; funext a; ring
    _ = ∑' a, p a * ∑' b, f a b * F b := by
        rw [ENNReal.tsum_comm]
        congr 1; funext a
        rw [ENNReal.tsum_mul_left]

theorem tsum_map_mul (p : PMF α) (f : α → β) (F : β → ℝ≥0∞) :
    ∑' b, p.map f b * F b = ∑' a, p a * F (f a) := by
  rw [← PMF.bind_pure_comp, tsum_bind_mul]
  simp only [Function.comp_apply, tsum_pure_mul]

/-- Wald's identity for `k` independent draws: `E (∑ F) = k E F`. -/
theorem tsum_iidList_mul_sum (p : PMF α) (F : α → ℝ≥0∞) (k : ℕ) :
    ∑' l, iidList p k l * (l.map F).sum = k * ∑' a, p a * F a := by
  induction k with
  | zero => simp [iidList]
  | succ k ih =>
    rw [iidList, tsum_bind_mul]
    simp only [tsum_map_mul, List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add,
      ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ih]
    push_cast; ring

/-- Second moments of a sum of `k` independent draws:
`E (∑ F)(∑ H) = k E[F H] + k (k - 1) E F E H`. -/
theorem tsum_iidList_mul_sum_mul_sum (p : PMF α) (F H : α → ℝ≥0∞) (k : ℕ) :
    ∑' l, iidList p k l * ((l.map F).sum * (l.map H).sum) =
      k * ∑' a, p a * (F a * H a) +
        ((k * (k - 1) : ℕ) : ℝ≥0∞) * ((∑' a, p a * F a) * ∑' a, p a * H a) := by
  induction k with
  | zero => simp [iidList]
  | succ k ih =>
    rw [iidList, tsum_bind_mul]
    have inner : ∀ a, ∑' l, (iidList p k).map (List.cons a) l *
        ((l.map F).sum * (l.map H).sum) =
        F a * H a + F a * (k * ∑' a, p a * H a) + H a * (k * ∑' a, p a * F a) +
          (k * ∑' a, p a * (F a * H a) +
            ((k * (k - 1) : ℕ) : ℝ≥0∞) * ((∑' a, p a * F a) * ∑' a, p a * H a)) := by
      intro a
      rw [tsum_map_mul]
      have e : ∀ l, iidList p k l * (((a :: l).map F).sum * ((a :: l).map H).sum) =
          iidList p k l * (F a * H a) + F a * (iidList p k l * (l.map H).sum) +
            H a * (iidList p k l * (l.map F).sum) +
              iidList p k l * ((l.map F).sum * (l.map H).sum) := by
        intro l; simp only [List.map_cons, List.sum_cons]; ring
      rw [tsum_congr e, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
        ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ENNReal.tsum_mul_left,
        ENNReal.tsum_mul_left, tsum_iidList_mul_sum, tsum_iidList_mul_sum, ih]
    simp only [inner]
    have e : ∀ a, p a * (F a * H a + F a * (k * ∑' a, p a * H a) +
        H a * (k * ∑' a, p a * F a) + (k * ∑' a, p a * (F a * H a) +
          ((k * (k - 1) : ℕ) : ℝ≥0∞) * ((∑' a, p a * F a) * ∑' a, p a * H a))) =
        p a * (F a * H a) + p a * F a * (k * ∑' a, p a * H a) +
          p a * H a * (k * ∑' a, p a * F a) + p a * (k * ∑' a, p a * (F a * H a) +
            ((k * (k - 1) : ℕ) : ℝ≥0∞) * ((∑' a, p a * F a) * ∑' a, p a * H a)) :=
      fun a => by ring
    rw [tsum_congr e, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
      ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, PMF.tsum_coe,
      one_mul]
    have hk : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by
      cases k with
      | zero => rfl
      | succ k => simp only [Nat.add_sub_cancel]; ring
    rw [hk]; push_cast; ring

/-- Random number of draws: `E (∑ F) = E N · E F`. The multiset form is the observation law of a
vertex in a branching process. -/
theorem tsum_bind_iidList_mul_sum (N : PMF ℕ) (p : PMF α) (F : α → ℝ≥0∞) :
    ∑' s, (N.bind fun k => (iidList p k).map (fun l : List α => (l : Multiset α))) s *
      (s.map F).sum = (∑' k, N k * k) * ∑' a, p a * F a := by
  rw [tsum_bind_mul, ← ENNReal.tsum_mul_right]
  congr 1; funext k
  rw [tsum_map_mul]
  simp only [Multiset.map_coe, Multiset.sum_coe, tsum_iidList_mul_sum, mul_assoc]

theorem tsum_bind_iidList_mul_sum_mul_sum (N : PMF ℕ) (p : PMF α) (F H : α → ℝ≥0∞) :
    ∑' s, (N.bind fun k => (iidList p k).map (fun l : List α => (l : Multiset α))) s *
      ((s.map F).sum * (s.map H).sum) =
      (∑' k, N k * k) * ∑' a, p a * (F a * H a) +
        (∑' k, N k * ((k * (k - 1) : ℕ) : ℝ≥0∞)) * ((∑' a, p a * F a) * ∑' a, p a * H a) := by
  rw [tsum_bind_mul, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  congr 1; funext k
  rw [tsum_map_mul]
  simp only [Multiset.map_coe, Multiset.sum_coe, tsum_iidList_mul_sum_mul_sum]
  ring

/-- From `ℝ≥0∞` moments to real ones. -/
theorem tsum_toReal_mul_toReal (p : PMF α) (X : α → ℝ≥0∞) (h : ∑' a, p a * X a ≠ ∞) :
    ∑' a, (p a).toReal * (X a).toReal = (∑' a, p a * X a).toReal := by
  rw [ENNReal.tsum_toReal_eq fun a => ENNReal.ne_top_of_tsum_ne_top h a]
  simp only [ENNReal.toReal_mul]

theorem summable_toReal_mul_toReal (p : PMF α) (X : α → ℝ≥0∞) (h : ∑' a, p a * X a ≠ ∞) :
    Summable fun a => (p a).toReal * (X a).toReal := by
  simpa only [ENNReal.toReal_mul] using ENNReal.summable_toReal h

end Wald

section Census

variable {ι : Type*} {O : ℕ → Type*} {K : ι → PMF ι} {N : PMF ℕ} {leaf : ι → O 0}
  {up : ∀ n, Multiset (O n) → O (n + 1)} {law : (n : ℕ) → ι → PMF (O n)}

/-- First moment of an additive statistic of a broadcast (for example the number of depth-`n`
vertices in a given state): `E_i X_{n+1} = E N · ∑ j, K i j · E_j X_n`. -/
theorem IsBroadcastLaw.tsum_mul_census (h : IsBroadcastLaw K N leaf up law)
    (X : (n : ℕ) → O n → ℝ≥0∞) (hX : ∀ n s, X (n + 1) (up n s) = (s.map (X n)).sum) (n : ℕ)
    (i : ι) :
    ∑' o, law (n + 1) i o * X (n + 1) o =
      (∑' k, N k * k) * ∑' j, K i j * ∑' o, law n j o * X n o := by
  rw [h.succ n i, tsum_bind_mul, ← ENNReal.tsum_mul_right]
  congr 1; funext k
  rw [tsum_map_mul]
  simp only [hX, Multiset.map_coe, Multiset.sum_coe, tsum_iidList_mul_sum, tsum_bind_mul]
  ring

/-- Second moments of additive statistics of a broadcast:
`E_i X_{n+1} Y_{n+1} = E N · ∑ j, K i j E_j[X_n Y_n] + E N(N-1) · (∑ j, K i j E_j X_n)
(∑ j, K i j E_j Y_n)`. -/
theorem IsBroadcastLaw.tsum_mul_census_mul_census (h : IsBroadcastLaw K N leaf up law)
    (X Y : (n : ℕ) → O n → ℝ≥0∞) (hX : ∀ n s, X (n + 1) (up n s) = (s.map (X n)).sum)
    (hY : ∀ n s, Y (n + 1) (up n s) = (s.map (Y n)).sum) (n : ℕ) (i : ι) :
    ∑' o, law (n + 1) i o * (X (n + 1) o * Y (n + 1) o) =
      (∑' k, N k * k) * ∑' j, K i j * ∑' o, law n j o * (X n o * Y n o) +
        (∑' k, N k * ((k * (k - 1) : ℕ) : ℝ≥0∞)) *
          ((∑' j, K i j * ∑' o, law n j o * X n o) * ∑' j, K i j * ∑' o, law n j o * Y n o) := by
  rw [h.succ n i, tsum_bind_mul, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right,
    ← ENNReal.tsum_add]
  congr 1; funext k
  rw [tsum_map_mul]
  simp only [hX, hY, Multiset.map_coe, Multiset.sum_coe, tsum_iidList_mul_sum_mul_sum,
    tsum_bind_mul]
  ring

end Census

section Offspring

open Nat in
theorem hasSum_poissonWeight (d : ℝ) : HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / k !) 1 := by
  convert! (NormedSpace.expSeries_div_hasSum_exp d).mul_left (Real.exp (-d)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← Real.exp_eq_exp_ℝ, ← Real.exp_add]

open Nat in
/-- Poisson mean: `∑ k, e^{-d} d^k / k! · k = d`. -/
theorem hasSum_poissonWeight_mul (d : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / k ! * k) d := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, sub_zero]
  convert (hasSum_poissonWeight d).mul_left d using 1
  swap; · ring
  funext n
  have h := (Nat.cast_pos (α := ℝ)).2 (Nat.factorial_pos n)
  rw [Nat.factorial_succ]; push_cast
  field_simp
  ring

open Nat in
/-- Poisson second factorial moment: `∑ k, e^{-d} d^k / k! · k (k - 1) = d^2`. -/
theorem hasSum_poissonWeight_mul_descFactorial (d : ℝ) :
    HasSum (fun k : ℕ => Real.exp (-d) * d ^ k / k ! * ((k * (k - 1) : ℕ) : ℝ)) (d ^ 2) := by
  rw [← hasSum_nat_add_iff' 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_sub, mul_zero, Nat.cast_zero,
    zero_add, Nat.sub_self, sub_zero]
  convert (hasSum_poissonWeight d).mul_left (d ^ 2) using 1
  swap; · ring
  funext n
  have h := (Nat.cast_pos (α := ℝ)).2 (Nat.factorial_pos n)
  simp only [Nat.factorial_succ]; push_cast
  field_simp
  ring

open Nat in
/-- The `ℝ≥0∞` mean of a Poisson law written with `ENNReal.ofReal` weights. -/
theorem tsum_ofReal_poissonWeight_mul {d : ℝ} (hd : 0 ≤ d) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-d) * d ^ k / k !) * k = ENNReal.ofReal d := by
  have hw : ∀ k : ℕ, 0 ≤ Real.exp (-d) * d ^ k / k ! := fun k => by positivity
  simp_rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (hw _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hw k) (Nat.cast_nonneg _))
    (hasSum_poissonWeight_mul d).summable, (hasSum_poissonWeight_mul d).tsum_eq]

open Nat in
theorem tsum_ofReal_poissonWeight_mul_descFactorial {d : ℝ} (hd : 0 ≤ d) :
    ∑' k : ℕ, ENNReal.ofReal (Real.exp (-d) * d ^ k / k !) * ((k * (k - 1) : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal (d ^ 2) := by
  have hw : ∀ k : ℕ, 0 ≤ Real.exp (-d) * d ^ k / k ! := fun k => by positivity
  simp_rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (hw _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hw k) (Nat.cast_nonneg _))
    (hasSum_poissonWeight_mul_descFactorial d).summable,
    (hasSum_poissonWeight_mul_descFactorial d).tsum_eq]

/-- Moments of a deterministic offspring number. -/
theorem tsum_pure_mul_natCast (b : ℕ) : ∑' k, PMF.pure b k * (k : ℝ≥0∞) = b :=
  tsum_pure_mul b fun k => (k : ℝ≥0∞)

end Offspring

end

end TheoremOS.Probability
