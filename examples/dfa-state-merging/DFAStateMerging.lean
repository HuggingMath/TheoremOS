import ArchivedFiniteCongruence
import Mathlib.Computability.DFA

open OAI.FiniteCongruence

namespace TheoremOS.DFAStateMerging

variable {Letter : Type*} {State : Type} [Fintype Letter]

/-- A transition for each letter is a unary operation on states. -/
noncomputable def transitionAlgebra (machine : DFA Letter State) : Algebra State where
  numOps := Fintype.card Letter
  arity := fun _ => 1
  op := fun index args => machine.step (args 0) ((Fintype.equivFin Letter).symm index)

private theorem related_step (machine : DFA Letter State)
    (relation : Congruence (transitionAlgebra machine)) {s t : State}
    (related : relation.1 s t) (letter : Letter) :
    relation.1 (machine.step s letter) (machine.step t letter) := by
  simpa [transitionAlgebra] using
    relation.2 (Fintype.equivFin Letter letter) (fun _ => s) (fun _ => t) (fun _ => related)

private theorem related_eval (machine : DFA Letter State)
    (relation : Congruence (transitionAlgebra machine)) (word : List Letter) {s t : State}
    (related : relation.1 s t) :
    relation.1 (machine.evalFrom s word) (machine.evalFrom t word) := by
  induction word generalizing s t with
  | nil => exact related
  | cons letter rest ih =>
    simpa only [DFA.evalFrom_cons] using ih (related_step machine relation related letter)

/-- The archived construction closes the proposed merges under transitions and equivalence. -/
noncomputable def stateCongruence (machine : DFA Letter State) (seeds : Finset (State × State)) :
    Congruence (transitionAlgebra machine) :=
  ⟨Relation.EqvGen.setoid (TranslateRel (transitionAlgebra machine) seeds),
    eqvGenTranslate_compatible (transitionAlgebra machine) seeds⟩

private theorem stateCongruence_seed (machine : DFA Letter State) {seeds : Finset (State × State)}
    {pair : State × State} (member : pair ∈ seeds) :
    (stateCongruence machine seeds).1 pair.1 pair.2 :=
  Relation.EqvGen.rel _ _ (seed_mem_translateRel (alg := transitionAlgebra machine) member)

private theorem stateCongruence_preserved (machine : DFA Letter State)
    (seeds : Finset (State × State)) (relation : Congruence (transitionAlgebra machine))
    (containsSeeds : ∀ pair ∈ seeds, relation.1 pair.1 pair.2) {s t : State}
    (related : (stateCongruence machine seeds).1 s t) : relation.1 s t := by
  change Relation.EqvGen (TranslateRel (transitionAlgebra machine) seeds) s t at related
  induction related with
  | rel _ _ translated =>
    obtain ⟨pair, member, f, compatible, rfl, rfl⟩ := translated
    exact compatible relation _ _ (containsSeeds pair member)
  | refl s => exact relation.1.refl s
  | symm _ _ _ ih => exact relation.1.symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact relation.1.trans ih₁ ih₂

private noncomputable def languageCongruence (machine : DFA Letter State) :
    Congruence (transitionAlgebra machine) := by
  refine ⟨Setoid.ker machine.acceptsFrom, ?_⟩
  intro index left right related
  apply Setoid.ker_def.mpr
  let letter := (Fintype.equivFin Letter).symm index
  have equalLanguages := Setoid.ker_def.mp (related (0 : Fin 1))
  ext word
  change letter :: word ∈ machine.acceptsFrom (left (0 : Fin 1)) ↔
    letter :: word ∈ machine.acceptsFrom (right (0 : Fin 1))
  rw [equalLanguages]

/-- Each quotient state must have one well-defined acceptance status. -/
def RespectsAcceptance (machine : DFA Letter State) (relation : Setoid State) : Prop :=
  ∀ ⦃s t⦄, relation s t → (s ∈ machine.accept ↔ t ∈ machine.accept)

/-- The generated merge is sound exactly when the proposed pairs accept the same continuations. -/
theorem merge_safe_iff (machine : DFA Letter State) (seeds : Finset (State × State)) :
    RespectsAcceptance machine (stateCongruence machine seeds).1 ↔
      ∀ pair ∈ seeds, machine.acceptsFrom pair.1 = machine.acceptsFrom pair.2 := by
  constructor
  · intro consistent pair member
    ext word
    exact consistent (related_eval machine (stateCongruence machine seeds) word
      (stateCongruence_seed machine member))
  · intro sameLanguage s t related
    have same : machine.acceptsFrom s = machine.acceptsFrom t :=
      stateCongruence_preserved machine seeds (languageCongruence machine) sameLanguage related
    change [] ∈ machine.acceptsFrom s ↔ [] ∈ machine.acceptsFrom t
    rw [same]

noncomputable def mergedDFA (machine : DFA Letter State) (seeds : Finset (State × State))
    (consistent : RespectsAcceptance machine (stateCongruence machine seeds).1) :
    DFA Letter (Quotient (stateCongruence machine seeds).1) where
  step state letter := Quotient.map (fun s => machine.step s letter)
    (fun _ _ h => related_step machine (stateCongruence machine seeds) h letter) state
  start := Quotient.mk _ machine.start
  accept := {state | Quotient.lift (fun s => s ∈ machine.accept)
    (fun _ _ h => propext (consistent h)) state}

private theorem merged_evalFrom (machine : DFA Letter State) (seeds : Finset (State × State))
    (consistent : RespectsAcceptance machine (stateCongruence machine seeds).1)
    (word : List Letter) (s : State) :
    (mergedDFA machine seeds consistent).evalFrom (Quotient.mk _ s) word =
      Quotient.mk _ (machine.evalFrom s word) := by
  induction word generalizing s with
  | nil => rfl
  | cons letter rest ih => exact ih (machine.step s letter)

/-- Reading a word in the quotient preserves acceptance. -/
theorem merged_accepts (machine : DFA Letter State) (seeds : Finset (State × State))
    (consistent : RespectsAcceptance machine (stateCongruence machine seeds).1) :
    (mergedDFA machine seeds consistent).accepts = machine.accepts := by
  ext word
  change (mergedDFA machine seeds consistent).evalFrom (Quotient.mk _ machine.start) word ∈
    (mergedDFA machine seeds consistent).accept ↔ machine.evalFrom machine.start word ∈ machine.accept
  rw [merged_evalFrom]
  rfl

/-- Reading `true` flips parity. Reading `false` flips the redundant bit. -/
def parityMachine : DFA Bool (Bool × Bool) where
  step state letter := (if letter then !state.1 else state.1,
    if letter then state.2 else !state.2)
  start := (false, false)
  accept := {state | state.1 = false}

def paritySeeds : Finset ((Bool × Bool) × (Bool × Bool)) :=
  {((false, false), (false, true))}

private theorem parity_evalFrom_even (word : List Bool) (state : Bool × Bool) :
    (parityMachine.evalFrom state word).1 = false ↔
      (word.count true + (if state.1 then 1 else 0)) % 2 = 0 := by
  induction word generalizing state with
  | nil =>
    obtain ⟨parity, copy⟩ := state
    cases parity <;> simp
  | cons letter rest ih =>
    rw [DFA.evalFrom_cons, ih]
    obtain ⟨parity, copy⟩ := state
    cases letter <;> cases parity <;> simp [parityMachine]
    omega

theorem parity_accepts_iff (word : List Bool) :
    word ∈ parityMachine.accepts ↔ word.count true % 2 = 0 := by
  change (parityMachine.evalFrom parityMachine.start word).1 = false ↔ _
  exact parity_evalFrom_even word (false, false)

private noncomputable def parityCongruence : Congruence (transitionAlgebra parityMachine) := by
  refine ⟨Setoid.ker Prod.fst, ?_⟩
  intro index _ _ related
  let letter := (Fintype.equivFin Bool).symm index
  exact congrArg (fun bit : Bool => if letter then !bit else bit) (related (0 : Fin 1))

/-- Merging the even copies forces the odd copies to merge, with no merge across parities. -/
theorem parity_merge_iff (s t : Bool × Bool) :
    (stateCongruence parityMachine paritySeeds).1 s t ↔ s.1 = t.1 := by
  constructor
  · intro related
    apply stateCongruence_preserved parityMachine paritySeeds parityCongruence _ related
    intro pair member
    have hp := Finset.mem_singleton.mp member
    subst pair
    rfl
  · obtain ⟨sParity, sCopy⟩ := s
    obtain ⟨tParity, tCopy⟩ := t
    intro equalParity
    change sParity = tParity at equalParity
    subst tParity
    have even : (stateCongruence parityMachine paritySeeds).1 (false, false) (false, true) :=
      stateCongruence_seed parityMachine (pair := ((false, false), (false, true))) (by simp [paritySeeds])
    have odd : (stateCongruence parityMachine paritySeeds).1 (true, false) (true, true) :=
      related_step parityMachine (stateCongruence parityMachine paritySeeds) even true
    let r := (stateCongruence parityMachine paritySeeds).1
    change r (sParity, sCopy) (sParity, tCopy)
    cases sParity <;> cases sCopy <;> cases tCopy <;>
      first | exact r.refl _ | exact even | exact odd | exact r.symm even | exact r.symm odd

/-- Both copies of both parity states are reachable from the start. -/
theorem parity_all_reachable (s : Bool × Bool) : ∃ word, parityMachine.eval word = s := by
  refine ⟨(if s.1 then [true] else []) ++ (if s.2 then [false] else []), ?_⟩
  rcases s with ⟨parity, copy⟩
  cases parity <;> cases copy <;> rfl

/-- The generated quotient has one state for each value of the parity bit. -/
noncomputable def parityQuotientEquiv :
    Quotient (stateCongruence parityMachine paritySeeds).1 ≃ Bool where
  toFun := Quotient.lift Prod.fst (fun _ _ h => (parity_merge_iff _ _).mp h)
  invFun bit := Quotient.mk _ (bit, false)
  left_inv := by
    intro state
    refine Quotient.inductionOn state fun s => ?_
    exact Quotient.sound ((parity_merge_iff _ _).mpr rfl)
  right_inv _ := rfl

theorem parity_accepts_preserved :
    (mergedDFA parityMachine paritySeeds (by
      intro s t related
      change s.1 = false ↔ t.1 = false
      rw [(parity_merge_iff s t).mp related])).accepts = parityMachine.accepts :=
  merged_accepts _ _ _

#print axioms merge_safe_iff
#print axioms merged_accepts
#print axioms parity_accepts_iff
#print axioms parity_merge_iff
#print axioms parity_all_reachable
#print axioms parityQuotientEquiv
#print axioms parity_accepts_preserved

end TheoremOS.DFAStateMerging
