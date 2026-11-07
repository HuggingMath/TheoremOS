import Mathlib

/-!
# Random k-SAT: counting, moments and the clause stream

Counting and probability facts behind the first- and second-moment method for random formulas.
Contents: for any clauses `C`, assignments `A` and relation `sat : C → A → Prop`, the formulas
`F : Fin m → C` satisfied by `a` number `s_a^m` with `s_a` the number of clauses `a` satisfies
(`natCard_forall_sat`); the **union bound** `#{satisfiable F} ≤ ∑_a s_a^m` and its ratio form
`#{satisfiable F} / |C|^m ≤ |A| (s/|C|)^m` when every `s_a ≤ s`; `N_{m+1} ≤ |C| N_m`, so the
satisfiable fraction is antitone in `m`; the **first moment** `∑_F X F = ∑_a s_a^m` and
**second moment** `∑_F (X F)^2 = ∑_{a,b} s_{ab}^m` of the number `X F` of satisfying assignments,
`s_{ab}` the number of clauses both satisfy, and the **second-moment method**
`(∑_F X F)^2 ≤ #{satisfiable F} ∑_F (X F)^2`. The **survival recursion** `filterStep sat`
(average of `f` over the solution sets `S.filter (sat c)`) iterated `m` times averages `f` over all
`m`-clause formulas (`filterStep_iterate`); from the indicator of non-emptiness it gives the
fraction of formulas that some assignment of `S` satisfies. For an i.i.d. clause stream
`Measure.infinitePi fun _ : ℕ => μ`: `P(first m clauses lie in t) = μ t ^ m`; the union bound
`P(some a ∈ S satisfies the first m clauses) ≤ ∑_{a ∈ S} P(a satisfies a clause)^m ≤ |S| q^m`;
almost sure eventual unsatisfiability when every `a ∈ S` fails a clause with positive
probability; and, for the uniform law on a finite clause type, the probability of an event about
the first `m` clauses is its share of the `|C|^m` formulas (`infinitePi_uniformOn_prefix`), with
the forms for "some `a ∈ S` satisfies the first `m` clauses", its complement, one clause falsifying
all of `S`, and the survival recursion. Clause models on `n` variables: `KClause n k` (a `k`-set
of variables with the value making each literal true) and `SignClause n k` (sign vectors
`Fin n → Option Bool` with `k` entries present), equivalent via `signClauseEquiv`; there are
`C(n,k) 2^k` clauses, an assignment satisfies `C(n,k) (2^k - 1)` and falsifies `C(n,k)`; the
clauses falsified by every assignment of `T ∋ a₀` number `C(d,k)` with `d` the number of variables
where `T` agrees with `a₀`; the clauses satisfied by both `a` and `b` number
`C(n,k) 2^k - 2 C(n,k) + C(z,k)` with `z` the number of variables where they agree. The
**first-moment bound** `P(satisfiable) ≤ 2^n (1 - 2^{-k})^m` for `m` uniform random clauses with
`k ≤ n`, in counting form for any clause model with these counts (`satisfiable_div_le_of_natCard`)
and in stream form (`infinitePi_uniformOn_exists_forall_sat_le_of_natCard`), and almost sure
eventual unsatisfiability of the uniform clause stream.

Sources: J. Franco and M. Paull, "Probabilistic analysis of the Davis–Putnam procedure for solving
the satisfiability problem", Discrete Appl. Math. 5 (1983), 77–87 (first-moment bound);
V. Chvátal and B. Reed, "Mick gets some (the odds are on his side)", FOCS 1992 (random k-SAT);
D. Achlioptas and C. Moore, "Random k-SAT: two moments suffice to cross a sharp threshold", SIAM
J. Comput. 36 (2006), 740–762 (second moment through pair overlaps); D. Achlioptas, "Random
satisfiability", Chapter 8 of *Handbook of Satisfiability*, IOS Press, 2009; N. Alon and
J. Spencer, *The Probabilistic Method*, 4th ed., Wiley, 2016, Chapter 4 (second-moment method).
Textbook material; nothing here is specific to a benchmark problem.

Bridges: a clause type defined as `(s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)` with
`Satisfies c a := ∃ v : c.1.1, a v = c.2 v` is `KClause n k` with `KClause.Sat` after unfolding,
so `natCard_kclause`, `natCard_kclause_sat`, `natCard_kclause_forall_not_sat` and
`exists_kclause_not_sat` close goals stated with it by `exact`; `rw` needs them restated first,
e.g. `have h : Nat.card (Clause n k) = n.choose k * 2 ^ k := natCard_kclause`. A sign-vector type
`{C : Fin n → Option Bool // (univ.filter fun i => (C i).isSome).card = k}` with
`∃ i, C.val i = some (σ i)` is `SignClause n k` with `SignClause.Sat`. Ratios written with
`Fintype.card` become `Nat.card` by `simp only [Fintype.card_eq_nat_card]`. A recursion
`f ↦ fun S => (∑ c, f (S.filter (Satisfies c))) / Fintype.card C` is `filterStep` by `rfl`. A stream
law `Measure.infinitePi fun _ => uniformOn Set.univ` on a clause type with its own `Fintype`,
`MeasurableSpace` and `MeasurableSingletonClass` instances matches the generic lemmas after
unfolding the law; supply `Nonempty` from `exists_kclause_not_sat`.
-/

namespace TheoremOS.Probability

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal

noncomputable section

section Count

variable {C A : Type*} (sat : C → A → Prop)

/-- The formulas `F : Fin m → C` satisfied by a fixed assignment are the `m`-tuples of clauses it
satisfies. -/
lemma natCard_forall_sat (a : A) (m : ℕ) :
    Nat.card {F : Fin m → C // ∀ j, sat (F j) a} = Nat.card {c // sat c a} ^ m := by
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin m) (c : C) => sat c a)),
    Nat.card_pi]
  simp

/-- **Union bound** over assignments: the number of satisfiable `m`-clause formulas is at most
`∑_a (number of clauses a satisfies)^m`. -/
lemma natCard_exists_forall_sat_le [Fintype A] [Finite C] (m : ℕ) :
    Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} ≤ ∑ a, Nat.card {c // sat c a} ^ m := by
  classical
  have := Fintype.ofFinite C
  simp_rw [← natCard_forall_sat sat, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc #{F : Fin m → C | ∃ a, ∀ j, sat (F j) a}
      = #(univ.biUnion fun a => ({F | ∀ j, sat (F j) a} : Finset (Fin m → C))) := by
        congr 1
        ext F
        simp
    _ ≤ _ := card_biUnion_le

/-- **First-moment bound** as a ratio: if every assignment satisfies at most `s` of the clauses,
the fraction of `m`-clause formulas that are satisfiable is at most `|A| (s/|C|)^m`. -/
lemma natCard_exists_forall_sat_div_le [Fintype A] [Finite C] (m s : ℕ)
    (hs : ∀ a, Nat.card {c // sat c a} ≤ s) :
    (Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} : ℝ) / Nat.card (Fin m → C) ≤
      Nat.card A * ((s : ℝ) / Nat.card C) ^ m := by
  have hN : Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} ≤ Nat.card A * s ^ m := by
    refine (natCard_exists_forall_sat_le sat m).trans ?_
    rw [Nat.card_eq_fintype_card, ← smul_eq_mul, ← Finset.card_univ]
    exact Finset.sum_le_card_nsmul _ _ _ fun a _ => Nat.pow_le_pow_left (hs a) m
  rw [Nat.card_fun, Nat.card_fin, Nat.cast_pow, div_pow, mul_div_assoc']
  gcongr
  exact_mod_cast hN

/-- One more clause can only lower the number of satisfiable formulas, relative to the number of
formulas: `N_{m+1} ≤ |C| N_m`. -/
lemma natCard_exists_forall_sat_succ_le [Finite C] (m : ℕ) :
    Nat.card {F : Fin (m + 1) → C // ∃ a, ∀ j, sat (F j) a} ≤
      Nat.card C * Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun F => (F.1 0, ⟨Fin.tail F.1, F.2.imp fun a ha j => ha j.succ⟩)) ?_
  intro F G h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  exact Subtype.ext ((Fin.cons_self_tail F.1).symm.trans (h.2 ▸ h.1 ▸ Fin.cons_self_tail G.1))

/-- The satisfiable fraction of `m`-clause formulas is antitone in `m`. -/
lemma natCard_exists_forall_sat_div_antitone [Finite C] :
    Antitone fun m => (Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} : ℝ) /
      Nat.card (Fin m → C) := by
  refine antitone_nat_of_succ_le fun m => ?_
  simp only [Nat.card_fun, Nat.card_fin, Nat.cast_pow]
  rcases (Nat.card C).eq_zero_or_pos with h0 | hpos
  · simp [h0]
    positivity
  have hc : (0 : ℝ) < Nat.card C := by exact_mod_cast hpos
  rw [div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
  have := natCard_exists_forall_sat_succ_le sat m
  have h' : (Nat.card {F : Fin (m + 1) → C // ∃ a, ∀ j, sat (F j) a} : ℝ) ≤
      Nat.card C * Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} := by exact_mod_cast this
  nlinarith [pow_pos hc m]

/-- **First moment**: summed over all formulas, the number of satisfying assignments is
`∑_a (number of clauses a satisfies)^m`. -/
lemma sum_natCard_sat [Fintype A] [Fintype C] (m : ℕ) :
    ∑ F : Fin m → C, Nat.card {a // ∀ j, sat (F j) a} = ∑ a, Nat.card {c // sat c a} ^ m := by
  classical
  simp_rw [← natCard_forall_sat sat, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]
  exact Finset.sum_comm

/-- **Second moment**: summed over all formulas, the square of the number of satisfying
assignments is `∑_{a,b} (number of clauses both a and b satisfy)^m`. -/
lemma sum_natCard_sat_sq [Fintype A] [Fintype C] (m : ℕ) :
    ∑ F : Fin m → C, Nat.card {a // ∀ j, sat (F j) a} ^ 2 =
      ∑ p : A × A, Nat.card {c // sat c p.1 ∧ sat c p.2} ^ m := by
  rw [← sum_natCard_sat (fun c (p : A × A) => sat c p.1 ∧ sat c p.2) m]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [sq, ← Nat.card_prod]
  refine Nat.card_congr ((Equiv.subtypeProdEquivProd).symm.trans (Equiv.subtypeEquivRight ?_))
  intro p
  simp only [forall_and]

/-- **Second-moment method**: the number of satisfiable formulas is at least
`(∑_F X F)^2 / ∑_F (X F)^2`, where `X F` is the number of assignments satisfying `F`. -/
lemma sq_sum_natCard_sat_le [Fintype A] [Fintype C] (m : ℕ) :
    ((∑ a, Nat.card {c // sat c a} ^ m : ℕ) : ℝ) ^ 2 ≤
      Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} *
        ((∑ p : A × A, Nat.card {c // sat c p.1 ∧ sat c p.2} ^ m : ℕ) : ℝ) := by
  classical
  rw [← sum_natCard_sat, ← sum_natCard_sat_sq]
  set X : (Fin m → C) → ℕ := fun F => Nat.card {a // ∀ j, sat (F j) a}
  have hX : ∀ F, X F ≠ 0 ↔ ∃ a, ∀ j, sat (F j) a := fun F => by
    rw [Nat.card_ne_zero, nonempty_subtype]
    exact and_iff_left inferInstance
  have hcard : Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} = #{F | X F ≠ 0} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp_rw [hX]
  rw [hcard, ← Finset.sum_filter_ne_zero, ← Finset.sum_filter_ne_zero (f := fun F => X F ^ 2)]
  push_cast
  simp_rw [show ∀ F, (X F ^ 2 ≠ 0) ↔ X F ≠ 0 from fun F => by simp]
  exact sq_sum_le_card_mul_sum_sq

end Count

section Average

variable {C A : Type*} [Fintype C] (sat : C → A → Prop) [DecidableRel sat]

/-- One step of the **survival recursion**: average `f` over the solution set left after one
uniformly random clause filters `S`. -/
def filterStep (f : Finset A → ℝ) (S : Finset A) : ℝ :=
  (∑ c : C, f (S.filter (sat c))) / Fintype.card C

/-- `m` steps of the survival recursion average `f` over all `m`-clause formulas:
`filterStep^[m] f S = |C|^{-m} ∑_F f {a ∈ S | a satisfies F}`. -/
lemma filterStep_iterate (f : Finset A → ℝ) (m : ℕ) (S : Finset A) :
    (filterStep sat)^[m] f S =
      (∑ F : Fin m → C, f (S.filter fun a => ∀ j, sat (F j) a)) / Fintype.card C ^ m := by
  induction m generalizing S with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', filterStep]
    simp_rw [ih, Finset.filter_filter]
    have he : ∀ g : (Fin (m + 1) → C) → ℝ, ∑ F, g F = ∑ p : C × (Fin m → C), g (Fin.cons p.1 p.2) :=
      fun g => (Fintype.sum_equiv (Fin.consEquiv fun _ => C) _ _ fun _ => rfl).symm
    rw [he, Fintype.sum_prod_type, ← Finset.sum_div, div_div, ← pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun F _ => ?_
    congr 1
    ext a
    simp [Fin.forall_fin_succ]

/-- The survival recursion started from the indicator of non-emptiness is the fraction of
`m`-clause formulas that some assignment in `S` satisfies. -/
lemma filterStep_iterate_nonempty (m : ℕ) (S : Finset A) :
    (filterStep sat)^[m] (fun T => if T.Nonempty then 1 else 0) S =
      (Nat.card {F : Fin m → C // ∃ a ∈ S, ∀ j, sat (F j) a} : ℝ) / Fintype.card C ^ m := by
  classical
  rw [filterStep_iterate, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun F _ => ?_
  simp [Finset.filter_nonempty_iff]

end Average

section Stream

variable {C A : Type*} [MeasurableSpace C] (sat : C → A → Prop)

/-- Under an i.i.d. clause stream the first `m` clauses all lie in `t` with probability
`μ t ^ m`. -/
lemma infinitePi_forall_lt_mem (μ : Measure C) [IsProbabilityMeasure μ] {t : Set C}
    (ht : MeasurableSet t) (m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) {ω | ∀ i < m, ω i ∈ t} = μ t ^ m := by
  have : {ω : ℕ → C | ∀ i < m, ω i ∈ t} = Set.pi (Finset.range m : Set ℕ) fun _ => t := by
    ext ω
    simp
  rw [this, Measure.infinitePi_pi _ fun _ _ => ht, Finset.prod_const, Finset.card_range]

section Countable

variable [MeasurableSingletonClass C] [Countable C]

/-- **Union bound** for an i.i.d. clause stream: some assignment of `S` satisfies the first `m`
clauses with probability at most `∑_{a ∈ S} P(a satisfies a clause)^m`. -/
lemma infinitePi_exists_forall_sat_le (μ : Measure C) [IsProbabilityMeasure μ] (S : Finset A)
    (m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) {ω | ∃ a ∈ S, ∀ i < m, sat (ω i) a} ≤
      ∑ a ∈ S, μ {c | sat c a} ^ m := by
  have : {ω : ℕ → C | ∃ a ∈ S, ∀ i < m, sat (ω i) a} =
      ⋃ a ∈ S, {ω | ∀ i < m, ω i ∈ {c | sat c a}} := by
    ext ω
    simp
  rw [this]
  refine (measure_biUnion_finset_le _ _).trans_eq (Finset.sum_congr rfl fun a _ => ?_)
  exact infinitePi_forall_lt_mem μ (Set.to_countable _).measurableSet m

/-- If each assignment of `S` satisfies a random clause with probability at most `q`, some
assignment of `S` satisfies the first `m` clauses with probability at most `|S| q^m`. -/
lemma infinitePi_exists_forall_sat_le_card_mul (μ : Measure C) [IsProbabilityMeasure μ]
    (S : Finset A) {q : ℝ≥0∞} (hq : ∀ a ∈ S, μ {c | sat c a} ≤ q) (m : ℕ) :
    Measure.infinitePi (fun _ : ℕ => μ) {ω | ∃ a ∈ S, ∀ i < m, sat (ω i) a} ≤
      #S * q ^ m := by
  refine (infinitePi_exists_forall_sat_le sat μ S m).trans ?_
  rw [← nsmul_eq_mul]
  exact Finset.sum_le_card_nsmul _ _ _ fun a ha => by gcongr; exact hq a ha

/-- If every assignment of `S` fails a random clause with positive probability, then almost
surely some finite prefix of the stream is satisfied by no assignment of `S`. -/
lemma infinitePi_forall_exists_forall_sat_eq_zero (μ : Measure C) [IsProbabilityMeasure μ]
    (S : Finset A) (hS : ∀ a ∈ S, μ {c | sat c a} < 1) :
    Measure.infinitePi (fun _ : ℕ => μ) {ω | ∀ m, ∃ a ∈ S, ∀ i < m, sat (ω i) a} = 0 := by
  set q := S.sup fun a => μ {c | sat c a}
  have hq1 : q < 1 := (Finset.sup_lt_iff (by simp)).2 hS
  have hsub : ∀ m, {ω : ℕ → C | ∀ m, ∃ a ∈ S, ∀ i < m, sat (ω i) a} ⊆
      {ω | ∃ a ∈ S, ∀ i < m, sat (ω i) a} := fun m ω hω => hω m
  have hle : ∀ m, Measure.infinitePi (fun _ : ℕ => μ)
      {ω | ∀ m, ∃ a ∈ S, ∀ i < m, sat (ω i) a} ≤ #S * q ^ m := fun m =>
    (measure_mono (hsub m)).trans (infinitePi_exists_forall_sat_le_card_mul sat μ S
      (fun a ha => Finset.le_sup (f := fun a => μ {c | sat c a}) ha) m)
  have ht : Tendsto (fun m => (#S : ℝ≥0∞) * q ^ m) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq1)
      (Or.inr (by simp))
  exact le_antisymm (ge_of_tendsto' ht hle) zero_le

end Countable

variable [MeasurableSingletonClass C] [Fintype C]

/-- Under the uniform law on a finite clause set, a fixed assignment satisfies a random clause
with probability (number of clauses it satisfies) / (number of clauses). -/
lemma uniformOn_univ_sat (a : A) :
    uniformOn (Set.univ : Set C) {c | sat c a} = Nat.card {c // sat c a} / Fintype.card C := by
  rw [uniformOn_univ, Measure.count_apply_finite _ (Set.toFinite _),
    ← Nat.card_eq_card_finite_toFinset]
  rfl

/-- An assignment that some clause falsifies satisfies a uniformly random clause with
probability `< 1`. -/
lemma uniformOn_univ_sat_lt_one {a : A} (h : ∃ c, ¬ sat c a) :
    uniformOn (Set.univ : Set C) {c | sat c a} < 1 := by
  classical
  rw [uniformOn_univ_sat]
  have hlt : Nat.card {c // sat c a} < Fintype.card C := by
    rw [Nat.card_eq_fintype_card]
    obtain ⟨c, hc⟩ := h
    exact Fintype.card_subtype_lt hc
  have hpos : (Fintype.card C : ℝ≥0∞) ≠ 0 := by
    have : Nonempty C := ⟨h.choose⟩
    simp
  rw [ENNReal.div_lt_iff (Or.inl hpos) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
  exact_mod_cast hlt

/-- Under the i.i.d. uniform stream on a finite clause set, an event about the first `m`
clauses has probability equal to its share of the `|C|^m` formulas with `m` clauses. -/
lemma infinitePi_uniformOn_prefix [Nonempty C] (m : ℕ) (P : (Fin m → C) → Prop) :
    (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | P fun j : Fin m => ω j}).toReal = (Nat.card {F // P F} : ℝ) / Fintype.card C ^ m := by
  classical
  set μ := uniformOn (Set.univ : Set C)
  let r : (ℕ → C) → (Fin m → C) := fun ω j => ω j
  have hr : Measurable r := by fun_prop
  have hmap : (Measure.infinitePi fun _ : ℕ => μ).map r = Measure.pi fun _ : Fin m => μ := by
    refine (Measure.pi_eq fun t ht => ?_).symm
    rw [Measure.map_apply hr (.univ_pi ht)]
    have : r ⁻¹' Set.univ.pi t = Set.pi (Finset.range m : Set ℕ)
        (fun i => if h : i < m then t ⟨i, h⟩ else Set.univ) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, Finset.coe_range, Set.mem_Iio, r]
      constructor
      · intro h i hi
        simpa [hi] using h ⟨i, hi⟩
      · intro h j
        simpa [j.2] using h j j.2
    rw [this, Measure.infinitePi_pi _ (fun i _ => by split_ifs <;> simp [ht _]), Finset.prod_range]
    simp
  have hpi : (Measure.pi fun _ : Fin m => μ) = uniformOn Set.univ := by
    have := uniformOn_pi (ι := Fin m) (f := fun _ => (Set.univ : Set C))
    rw [Set.pi_univ] at this
    exact this.symm
  have hset : {ω : ℕ → C | P fun j : Fin m => ω j} = r ⁻¹' {F | P F} := rfl
  rw [hset, ← Measure.map_apply hr (Set.toFinite _).measurableSet, hmap, hpi, uniformOn_univ,
    Measure.count_apply_finite _ (Set.toFinite _), ← Nat.card_eq_card_finite_toFinset,
    ENNReal.toReal_div]
  simp [Fintype.card_subtype]

/-- Under the i.i.d. uniform clause stream, the probability that some assignment of `S`
satisfies the first `m` clauses is the fraction of `m`-clause formulas that one of them
satisfies. -/
lemma infinitePi_uniformOn_exists_forall_sat [Nonempty C] (S : Finset A) (m : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | ∃ a ∈ S, ∀ i < m, sat (ω i) a}).toReal =
      (Nat.card {F : Fin m → C // ∃ a ∈ S, ∀ j, sat (F j) a} : ℝ) / Fintype.card C ^ m := by
  have : {ω : ℕ → C | ∃ a ∈ S, ∀ i < m, sat (ω i) a} =
      {ω | ∃ a ∈ S, ∀ j : Fin m, sat (ω j) a} := by
    ext ω
    simp [Fin.forall_iff]
  rw [this]
  exact infinitePi_uniformOn_prefix m fun F => ∃ a ∈ S, ∀ j, sat (F j) a

/-- The complementary event: no assignment of `S` satisfies the first `m` clauses. -/
lemma infinitePi_uniformOn_not_exists_forall_sat [Nonempty C] (S : Finset A) (m : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | ¬ ∃ a ∈ S, ∀ i < m, sat (ω i) a}).toReal =
      1 - (Nat.card {F : Fin m → C // ∃ a ∈ S, ∀ j, sat (F j) a} : ℝ) / Fintype.card C ^ m := by
  classical
  have : {ω : ℕ → C | ¬ ∃ a ∈ S, ∀ i < m, sat (ω i) a} =
      {ω | ¬ ∃ a ∈ S, ∀ j : Fin m, sat (ω j) a} := by
    ext ω
    simp [Fin.forall_iff]
  have hc : (0 : ℝ) < Fintype.card C ^ m := by positivity
  rw [this, infinitePi_uniformOn_prefix m fun F => ¬ ∃ a ∈ S, ∀ j, sat (F j) a,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Nat.card_eq_fintype_card,
    Nat.cast_sub (Fintype.card_subtype_le _), Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    sub_div, div_self hc.ne']

/-- The survival recursion started from the indicator of non-emptiness is the probability, under
the i.i.d. uniform clause stream, that some assignment of `S` satisfies the first `m` clauses. -/
lemma filterStep_iterate_nonempty_eq_infinitePi [Nonempty C] [DecidableRel sat] (S : Finset A)
    (m : ℕ) :
    (filterStep sat)^[m] (fun T => if T.Nonempty then 1 else 0) S =
      (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
        {ω | ∃ a ∈ S, ∀ i < m, sat (ω i) a}).toReal := by
  rw [filterStep_iterate_nonempty, infinitePi_uniformOn_exists_forall_sat]

/-- One clause of the i.i.d. uniform stream falsifies every assignment of `S` with probability
(number of clauses falsifying all of `S`) / (number of clauses). -/
lemma infinitePi_uniformOn_forall_not_sat_one [Nonempty C] (S : Finset A) :
    (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | ¬ ∃ a ∈ S, ∀ i < 1, sat (ω i) a}).toReal =
      (Nat.card {c // ∀ a ∈ S, ¬ sat c a} : ℝ) / Fintype.card C := by
  have : {ω : ℕ → C | ¬ ∃ a ∈ S, ∀ i < 1, sat (ω i) a} =
      {ω | (fun F : Fin 1 → C => ∀ a ∈ S, ¬ sat (F 0) a) fun j => ω j} := by
    ext ω
    simp
  rw [this, infinitePi_uniformOn_prefix 1 fun F => ∀ a ∈ S, ¬ sat (F 0) a, pow_one]
  congr 2
  exact Nat.card_congr ((Equiv.funUnique (Fin 1) C).subtypeEquiv fun F => Iff.rfl)

end Stream

section KClause

variable {n k : ℕ}

/-- A **`k`-clause** on `n` variables: a set of `k` variables together with, for each of them,
the value that makes its literal true. -/
abbrev KClause (n k : ℕ) := (s : {s : Finset (Fin n) // s.card = k}) × (s.1 → Bool)

/-- An assignment satisfies a `k`-clause when it agrees with it on some variable of the clause. -/
def KClause.Sat (c : KClause n k) (a : Fin n → Bool) : Prop := ∃ v : c.1.1, a v = c.2 v

/-- There are `C(n,k) 2^k` clauses of width `k` on `n` variables. -/
lemma natCard_kclause : Nat.card (KClause n k) = n.choose k * 2 ^ k := by
  rw [Nat.card_sigma]
  have : ∀ s : {s : Finset (Fin n) // s.card = k}, Nat.card (s.1 → Bool) = 2 ^ k := fun s => by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
      Nat.card_eq_fintype_card, Fintype.card_coe, s.2]
  simp_rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len, Fintype.card_fin,
    smul_eq_mul]

/-- The clauses falsified by every assignment of a set `T ∋ a₀` are the clauses on `k` variables
where all of `T` agrees with `a₀`, with the literals that `a₀` falsifies: there are
`C(d, k)` of them, `d` the number of such variables. -/
lemma natCard_kclause_forall_not_sat (T : Finset (Fin n → Bool)) {a₀ : Fin n → Bool}
    (h₀ : a₀ ∈ T) :
    Nat.card {c : KClause n k // ∀ a ∈ T, ¬ c.Sat a} =
      (#{v | ∀ a ∈ T, a v = a₀ v}).choose k := by
  classical
  set D : Finset (Fin n) := {v | ∀ a ∈ T, a v = a₀ v}
  have hσ : ∀ c : KClause n k, (∀ a ∈ T, ¬ c.Sat a) → ∀ v, c.2 v = !a₀ v := fun c hc v => by
    have h : ¬ a₀ v = c.2 v := fun h => hc a₀ h₀ ⟨v, h⟩
    cases h1 : c.2 v <;> cases h2 : a₀ v <;> simp_all
  rw [← Finset.card_powersetCard, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun c => ⟨c.1.1.1, Finset.mem_powersetCard.2 ⟨fun v hv => ?_, c.1.1.2⟩⟩
      invFun := fun s => ⟨⟨⟨s.1, (Finset.mem_powersetCard.1 s.2).2⟩, fun v => !a₀ v⟩, ?_⟩
      left_inv := ?_
      right_inv := fun s => rfl }
  · simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha
    have h3 : ¬ a v = c.1.2 ⟨v, hv⟩ := fun h => c.2 a ha ⟨⟨v, hv⟩, h⟩
    rw [hσ c.1 c.2 ⟨v, hv⟩] at h3
    cases h : a v <;> cases h' : a₀ v <;> simp_all
  · intro a ha ⟨v, hv⟩
    have hvD := (Finset.mem_powersetCard.1 s.2).1 v.2
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hvD
    rw [hvD a ha] at hv
    cases h : a₀ v <;> simp_all
  · rintro ⟨⟨s, σ⟩, hc⟩
    have := hσ ⟨s, σ⟩ hc
    simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
    exact funext fun v => (this v).symm

/-- A fixed assignment falsifies exactly `C(n,k)` of the `k`-clauses. -/
lemma natCard_kclause_not_sat (a : Fin n → Bool) :
    Nat.card {c : KClause n k // ¬ c.Sat a} = n.choose k := by
  have := natCard_kclause_forall_not_sat (k := k) {a} (Finset.mem_singleton_self a)
  simp only [Finset.mem_singleton, forall_eq] at this
  rw [this]
  simp

/-- A fixed assignment satisfies exactly `C(n,k) (2^k - 1)` of the `k`-clauses. -/
lemma natCard_kclause_sat (a : Fin n → Bool) :
    Nat.card {c : KClause n k // c.Sat a} = n.choose k * (2 ^ k - 1) := by
  classical
  have h := Nat.card_congr (Equiv.sumCompl fun c : KClause n k => c.Sat a)
  rw [Nat.card_sum, natCard_kclause, natCard_kclause_not_sat] at h
  rw [Nat.mul_sub_one]
  omega

/-- **Pair count** for the second moment: the clauses satisfied by both `a` and `b` number
`C(n,k) 2^k - 2 C(n,k) + C(z,k)`, `z` the number of variables where `a` and `b` agree. -/
lemma natCard_kclause_sat_and (a b : Fin n → Bool) :
    Nat.card {c : KClause n k // c.Sat a ∧ c.Sat b} + 2 * n.choose k =
      n.choose k * 2 ^ k + (#{v | a v = b v}).choose k := by
  classical
  have hz := natCard_kclause_forall_not_sat (k := k) {a, b}
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  have hz' : (#{v | ∀ x ∈ ({a, b} : Finset (Fin n → Bool)), x v = b v}) = #{v | a v = b v} := by
    congr 1
    ext v
    simp
  rw [hz'] at hz
  have ha := natCard_kclause_not_sat (k := k) a
  have hb := natCard_kclause_not_sat (k := k) b
  have hN := natCard_kclause (n := n) (k := k)
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at hz ha hb hN ⊢
  have hu := Finset.card_union_add_card_inter
    ({c | ¬ c.Sat a} : Finset (KClause n k)) {c | ¬ c.Sat b}
  have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (KClause n k)))
    fun c : KClause n k => c.Sat a ∧ c.Sat b
  rw [← Finset.filter_or, ← Finset.filter_and] at hu
  have e1 : ({c | ¬ c.Sat a ∨ ¬ c.Sat b} : Finset (KClause n k)) =
      ({c | ¬ (c.Sat a ∧ c.Sat b)} : Finset (KClause n k)) :=
    Finset.filter_congr fun c _ => by tauto
  have e2 : ({c | ¬ c.Sat a ∧ ¬ c.Sat b} : Finset (KClause n k)) =
      ({c | ∀ x ∈ ({a, b} : Finset (Fin n → Bool)), ¬ c.Sat x} : Finset (KClause n k)) :=
    Finset.filter_congr fun c _ => by simp
  rw [e1, e2, hz, ha, hb] at hu
  rw [Finset.card_univ] at hc
  omega

/-- For `k ≤ n` some `k`-clause falsifies any given assignment. -/
lemma exists_kclause_not_sat (hk : k ≤ n) (a : Fin n → Bool) : ∃ c : KClause n k, ¬ c.Sat a := by
  have h : 0 < Nat.card {c : KClause n k // ¬ c.Sat a} := by
    rw [natCard_kclause_not_sat]
    exact Nat.choose_pos hk
  obtain ⟨⟨c, hc⟩⟩ := (Nat.card_pos_iff.1 h).1
  exact ⟨c, hc⟩

end KClause

section SignClause

variable {n k : ℕ}

/-- A `k`-clause as a **sign vector**: each variable is absent (`none`) or carries the value that
makes its literal true, and exactly `k` variables are present. -/
abbrev SignClause (n k : ℕ) :=
  {C : Fin n → Option Bool // (Finset.univ.filter fun i => (C i).isSome).card = k}

/-- An assignment satisfies a sign-vector clause when it agrees with it on a present variable. -/
def SignClause.Sat (C : SignClause n k) (a : Fin n → Bool) : Prop := ∃ i, C.1 i = some (a i)

/-- Two `k`-clauses with the same variables and the same literal values are equal. -/
lemma KClause.ext {c d : KClause n k} (h : c.1.1 = d.1.1)
    (h' : ∀ v (hc : v ∈ c.1.1) (hd : v ∈ d.1.1), c.2 ⟨v, hc⟩ = d.2 ⟨v, hd⟩) : c = d := by
  obtain ⟨⟨s, hs⟩, σ⟩ := c
  obtain ⟨⟨t, ht⟩, τ⟩ := d
  simp only at h
  subst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  exact funext fun v => h' v.1 v.2 v.2

/-- Sign vectors and (variable set, literal values) pairs are the same `k`-clauses. -/
def signClauseEquiv : SignClause n k ≃ KClause n k where
  toFun C := ⟨⟨Finset.univ.filter fun i => (C.1 i).isSome, C.2⟩, fun v => (C.1 v).getD false⟩
  invFun c := ⟨fun i => if h : i ∈ c.1.1 then some (c.2 ⟨i, h⟩) else none, by
    refine Eq.trans ?_ c.1.2
    congr 1
    ext i
    by_cases h : i ∈ c.1.1 <;> simp [h]⟩
  left_inv C := by
    refine Subtype.ext (funext fun i => ?_)
    cases h : C.1 i <;> simp [h]
  right_inv c := by
    refine KClause.ext ?_ fun v hc hd => ?_
    · ext i
      by_cases h : i ∈ c.1.1 <;> simp [h]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      simp [hd]

/-- `signClauseEquiv` preserves satisfaction. -/
lemma signClauseEquiv_sat (C : SignClause n k) (a : Fin n → Bool) :
    (signClauseEquiv C).Sat a ↔ C.Sat a := by
  simp only [KClause.Sat, SignClause.Sat, signClauseEquiv, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Option.isSome_iff_exists] at hv
    obtain ⟨b, hb⟩ := hv
    exact ⟨v, by simp_all⟩
  · rintro ⟨i, h⟩
    exact ⟨⟨i, by simp [h]⟩, by simp [h]⟩

/-- There are `C(n,k) 2^k` sign-vector clauses of width `k`. -/
lemma natCard_signClause : Nat.card (SignClause n k) = n.choose k * 2 ^ k := by
  rw [Nat.card_congr signClauseEquiv, natCard_kclause]

/-- A fixed assignment satisfies exactly `C(n,k) (2^k - 1)` sign-vector clauses. -/
lemma natCard_signClause_sat (a : Fin n → Bool) :
    Nat.card {C : SignClause n k // C.Sat a} = n.choose k * (2 ^ k - 1) := by
  rw [← natCard_kclause_sat a]
  exact Nat.card_congr (signClauseEquiv.subtypeEquiv fun C => (signClauseEquiv_sat C a).symm)

end SignClause

section FirstMoment

/-- **First-moment bound for random `k`-SAT** in any clause model with `C(n,k) 2^k` clauses of
which each assignment satisfies `C(n,k) (2^k - 1)` (`k ≤ n`): the fraction of `m`-clause formulas
that are satisfiable is at most `2^n (1 - 2^{-k})^m`. -/
lemma satisfiable_div_le_of_natCard {n k : ℕ} {C : Type*} [Finite C]
    (sat : C → (Fin n → Bool) → Prop) (hk : k ≤ n) (hN : Nat.card C = n.choose k * 2 ^ k)
    (hs : ∀ a, Nat.card {c // sat c a} = n.choose k * (2 ^ k - 1)) (m : ℕ) :
    (Nat.card {F : Fin m → C // ∃ a, ∀ j, sat (F j) a} : ℝ) / Nat.card (Fin m → C) ≤
      2 ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ m := by
  have h := natCard_exists_forall_sat_div_le sat m (n.choose k * (2 ^ k - 1)) fun a => (hs a).le
  have hA : Nat.card (Fin n → Bool) = 2 ^ n := by simp
  have hpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  rw [hA, hN] at h
  convert h using 3
  · push_cast
    ring
  · rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h1, Nat.cast_pow]
    field_simp
    ring

/-- The first-moment bound for `k`-clauses. -/
lemma natCard_kclause_satisfiable_div_le {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Nat.card {F : Fin m → KClause n k // ∃ a, ∀ j, (F j).Sat a} : ℝ) /
      Nat.card (Fin m → KClause n k) ≤ 2 ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ m :=
  satisfiable_div_le_of_natCard (fun c a => KClause.Sat c a) hk natCard_kclause
    natCard_kclause_sat m

/-- The first-moment bound for sign-vector clauses. -/
lemma natCard_signClause_satisfiable_div_le {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Nat.card {F : Fin m → SignClause n k // ∃ a, ∀ j, (F j).Sat a} : ℝ) /
      Nat.card (Fin m → SignClause n k) ≤ 2 ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ m :=
  satisfiable_div_le_of_natCard (fun C a => SignClause.Sat C a) hk natCard_signClause
    natCard_signClause_sat m

section StreamModel

variable {n k : ℕ} {C : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  (sat : C → (Fin n → Bool) → Prop)

/-- **First-moment bound, stream form**: under the i.i.d. uniform stream on a clause model with
`C(n,k) 2^k` clauses of which each assignment satisfies `C(n,k) (2^k - 1)` (`k ≤ n`), some
assignment satisfies the first `m` clauses with probability at most `2^n (1 - 2^{-k})^m`. -/
lemma infinitePi_uniformOn_exists_forall_sat_le_of_natCard (hk : k ≤ n)
    (hN : Nat.card C = n.choose k * 2 ^ k)
    (hs : ∀ a, Nat.card {c // sat c a} = n.choose k * (2 ^ k - 1)) (m : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | ∃ a, ∀ i < m, sat (ω i) a}).toReal ≤ 2 ^ n * (1 - ((2 : ℝ) ^ k)⁻¹) ^ m := by
  have : Nonempty C := by
    have h : 0 < Nat.card C := by rw [hN]; exact Nat.mul_pos (Nat.choose_pos hk) (by positivity)
    exact (Nat.card_pos_iff.1 h).1
  have e : {ω : ℕ → C | ∃ a, ∀ i < m, sat (ω i) a} =
      {ω | ∃ a ∈ (Finset.univ : Finset (Fin n → Bool)), ∀ i < m, sat (ω i) a} := by
    simp
  have h := satisfiable_div_le_of_natCard sat hk hN hs m
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := C)] at h
  rw [e, infinitePi_uniformOn_exists_forall_sat]
  simpa using h

/-- Under the i.i.d. uniform stream on a clause model in which every assignment is falsified by
some clause, almost surely some finite prefix is unsatisfiable. -/
lemma infinitePi_uniformOn_forall_exists_forall_sat_eq_zero [Nonempty C]
    (h : ∀ a, ∃ c, ¬ sat c a) :
    Measure.infinitePi (fun _ : ℕ => uniformOn (Set.univ : Set C))
      {ω | ∀ m, ∃ a, ∀ i < m, sat (ω i) a} = 0 := by
  have := infinitePi_forall_exists_forall_sat_eq_zero sat (uniformOn (Set.univ : Set C))
    Finset.univ fun a _ => uniformOn_univ_sat_lt_one sat (h a)
  simpa using this

end StreamModel

end FirstMoment

end

end TheoremOS.Probability
