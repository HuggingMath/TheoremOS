import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Setoid.Basic
import Mathlib.Order.Hom.Basic

namespace OAI

namespace FiniteCongruence

structure Algebra (Carrier : Type) where
  numOps : ℕ
  arity : Fin numOps → ℕ
  op : (index : Fin numOps) → (Fin (arity index) → Carrier) → Carrier

def Compatible {Carrier : Type} (alg : Algebra Carrier) (rel : Setoid Carrier) : Prop :=
  ∀ (index : Fin alg.numOps) (left right : Fin (alg.arity index) → Carrier),
    (∀ coord, rel (left coord) (right coord)) → rel (alg.op index left) (alg.op index right)

def Congruence {Carrier : Type} (alg : Algebra Carrier) :=
  {rel : Setoid Carrier // Compatible alg rel}

instance {Carrier : Type} (alg : Algebra Carrier) : PartialOrder (Congruence alg) :=
  inferInstanceAs (PartialOrder {rel : Setoid Carrier // Compatible alg rel})

def Representable (Lat : Type) [PartialOrder Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ alg : Algebra (Fin size), Nonempty (Lat ≃o Congruence alg)

def Admissible {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (placement : Carrier → Carrier) : Prop :=
  ∀ left right, color (placement left) (placement right) ≤ color left right

def Marked {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  ∃ placement : Carrier → Carrier, Admissible color placement ∧
    ∃ edge ∈ seeds, placement edge.1 = left ∧ placement edge.2 = right

def Connected {Lat Carrier : Type} [LE Lat] (color : Carrier → Carrier → Lat)
    (seeds : Finset (Carrier × Carrier)) (left right : Carrier) : Prop :=
  Relation.EqvGen (Marked color seeds) left right

def IsGraphWitness {Lat Carrier : Type} [Lattice Lat] [OrderBot Lat]
    (color : Carrier → Carrier → Lat) : Prop :=
  (∀ left right, color left right = color right left) ∧
  (∀ left right, color left right = ⊥ ↔ left = right) ∧
  (∀ left right middle, color left right ≤ color left middle ⊔ color middle right) ∧
  (∀ lower upper : Lat, ¬ lower ≤ upper →
    ∃ left right, color left right ≤ lower ∧ ¬ color left right ≤ upper) ∧
  (∀ seeds : Finset (Carrier × Carrier), seeds.Nonempty → ∀ left right,
    color left right ≤ seeds.sup (fun edge => color edge.1 edge.2) →
      Connected color seeds left right)

def HasGraphWitness (Lat : Type) [Lattice Lat] [OrderBot Lat] : Prop :=
  ∃ size : ℕ, 0 < size ∧ ∃ color : Fin size → Fin size → Lat, IsGraphWitness color

def Principal {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier) : Congruence alg where
  val :=
    { r := fun a b => ∀ θ : Congruence alg, θ.1 x y → θ.1 a b
      iseqv :=
        { refl := fun a θ _ => θ.1.refl a
          symm := fun h θ hxy => θ.1.symm (h θ hxy)
          trans := fun hab hbc θ hxy => θ.1.trans (hab θ hxy) (hbc θ hxy) } }
  property := by
    intro index left right h θ hxy
    exact θ.2 index left right (fun coord => h coord θ hxy)
theorem principal_rel_iff {Carrier : Type} (alg : Algebra Carrier) (x y a b : Carrier) :
    (Principal alg x y).1 a b ↔ ∀ θ : Congruence alg, θ.1 x y → θ.1 a b :=
  Iff.rfl
theorem Principal_mem_self {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier) :
    (Principal alg x y).1 x y := by
  rw [principal_rel_iff]
  intro θ h
  exact h
theorem Principal_le_iff {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier)
    (θ : Congruence alg) : Principal alg x y ≤ θ ↔ θ.1 x y := by
  change (Principal alg x y).1 ≤ θ.1 ↔ θ.1 x y
  rw [Setoid.le_def]
  constructor
  · intro h
    exact h (Principal_mem_self alg x y)
  · intro h a b hab
    exact (principal_rel_iff alg x y a b).1 hab θ h
theorem Principal_least {Carrier : Type} (alg : Algebra Carrier) {x y : Carrier}
    (θ : Congruence alg) (h : θ.1 x y) : Principal alg x y ≤ θ :=
  (Principal_le_iff alg x y θ).2 h
theorem Principal_comm {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier) :
    Principal alg x y = Principal alg y x := by
  apply Subtype.ext
  apply Setoid.ext
  intro a b
  rw [principal_rel_iff, principal_rel_iff]
  constructor
  · intro h θ hyx
    exact h θ (θ.1.symm hyx)
  · intro h θ hxy
    exact h θ (θ.1.symm hxy)
theorem Principal_trans_le {Carrier : Type} (alg : Algebra Carrier) {x y z : Carrier}
    (θ : Congruence alg) (hxz : θ.1 x z) (hzy : θ.1 z y) : Principal alg x y ≤ θ :=
  Principal_least alg θ (θ.1.trans hxz hzy)
def Principal_diagonal {Carrier : Type} (alg : Algebra Carrier) : Congruence alg where
  val :=
    { r := fun a b => a = b
      iseqv :=
        { refl := fun _ => rfl
          symm := fun h => h.symm
          trans := fun h₁ h₂ => h₁.trans h₂ } }
  property := by
    intro index left right h
    have hlr : left = right := funext fun coord => h coord
    rw [hlr]
theorem Principal_diagonal_le {Carrier : Type} (alg : Algebra Carrier)
    (θ : Congruence alg) : Principal_diagonal alg ≤ θ := by
  intro a b h
  subst h
  exact θ.1.refl a
theorem Principal_eq_diagonal_iff {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier) :
    Principal alg x y = Principal_diagonal alg ↔ x = y := by
  constructor
  · intro h
    have hm : (Principal alg x y).1 x y := Principal_mem_self alg x y
    rw [h] at hm
    exact hm
  · intro h
    subst h
    apply le_antisymm
    · apply (Principal_le_iff alg x x (Principal_diagonal alg)).2
      rfl
    · exact Principal_diagonal_le alg (Principal alg x x)
instance principalBotCongruence {Carrier : Type} (alg : Algebra Carrier) : Bot (Congruence alg) :=
  ⟨Principal_diagonal alg⟩
theorem principal_bot_iff {Carrier : Type} (alg : Algebra Carrier) (x y : Carrier) :
    Principal alg x y = ⊥ ↔ x = y := by
  change Principal alg x y = Principal_diagonal alg ↔ x = y
  exact Principal_eq_diagonal_iff alg x y
def PolyCompatible {Carrier : Type} (alg : Algebra Carrier) (f : Carrier → Carrier) : Prop :=
  ∀ (θ : Congruence alg) (u v : Carrier), θ.1 u v → θ.1 (f u) (f v)
theorem polyCompatible_sanity {Carrier : Type} (alg : Algebra Carrier) :
    (PolyCompatible alg (fun x : Carrier => x) ∧
     ∀ (f g : Carrier → Carrier), PolyCompatible alg f → PolyCompatible alg g →
       PolyCompatible alg (fun x : Carrier => f (g x))) := by
  refine ⟨?_, ?_⟩
  · intro θ u v huv; exact huv
  · intro f g hf hg θ u v huv
    exact hf θ _ _ (hg θ u v huv)

-- R closed under compatible maps  =>  EqvGen R closed under compatible maps
theorem eqvGen_closed_of_closed {Carrier : Type} {R : Carrier → Carrier → Prop}
    (g : Carrier → Carrier) (hgm : ∀ x y, R x y → R (g x) (g y)) :
    ∀ x y, Relation.EqvGen R x y → Relation.EqvGen R (g x) (g y) := by
  intro x y h
  induction h with
  | rel a b hab => exact Relation.EqvGen.rel _ _ (hgm a b hab)
  | refl a => exact Relation.EqvGen.refl _
  | symm a b hab ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc => exact Relation.EqvGen.trans _ _ _ ihab ihbc
def TranslateRel {Carrier : Type} (alg : Algebra Carrier) (S : Finset (Carrier × Carrier))
    (u v : Carrier) : Prop :=
  ∃ p ∈ S, ∃ f : Carrier → Carrier, PolyCompatible alg f ∧ u = f p.1 ∧ v = f p.2
theorem polyCompatible_comp {Carrier : Type} {alg : Algebra Carrier} {f g : Carrier → Carrier}
    (hf : PolyCompatible alg f) (hg : PolyCompatible alg g) :
    PolyCompatible alg (fun x => f (g x)) := fun θ u v h => hf θ _ _ (hg θ u v h)
theorem translateRel_closed {Carrier : Type} {alg : Algebra Carrier}
    {S : Finset (Carrier × Carrier)} {g : Carrier → Carrier} (hg : PolyCompatible alg g) :
    ∀ x y, TranslateRel alg S x y → TranslateRel alg S (g x) (g y) := by
  rintro x y ⟨p, hp, f, hf, rfl, rfl⟩
  exact ⟨p, hp, fun z => g (f z), polyCompatible_comp (alg := alg) hg hf, rfl, rfl⟩
theorem eqvGenTranslate_closed {Carrier : Type} {alg : Algebra Carrier}
    {S : Finset (Carrier × Carrier)} {g : Carrier → Carrier} (hg : PolyCompatible alg g) :
    ∀ x y, Relation.EqvGen (TranslateRel alg S) x y →
      Relation.EqvGen (TranslateRel alg S) (g x) (g y) :=
  eqvGen_closed_of_closed g (translateRel_closed (S := S) hg)
theorem coord_map_polyCompatible {Carrier : Type} (alg : Algebra Carrier)
    (index : Fin alg.numOps) (u : Fin (alg.arity index) → Carrier)
    (c : Fin (alg.arity index)) :
    PolyCompatible alg (fun x : Carrier => alg.op index (Function.update u c x)) := by
  intro θ l r hlr
  apply θ.2 index
  intro coord
  by_cases h : coord = c
  · subst h
    simpa using hlr
  · rw [Function.update_of_ne h, Function.update_of_ne h]
theorem op_eqvGen_of_forall {Carrier : Type} (alg : Algebra Carrier)
    (S : Finset (Carrier × Carrier)) (index : Fin alg.numOps)
    (u v : Fin (alg.arity index) → Carrier)
    (huv : ∀ c, Relation.EqvGen (TranslateRel alg S) (u c) (v c)) :
    Relation.EqvGen (TranslateRel alg S) (alg.op index u) (alg.op index v) := by
  let w : Finset (Fin (alg.arity index)) → (Fin (alg.arity index) → Carrier) :=
    fun T c => if c ∈ T then v c else u c
  have hw_empty : w ∅ = u := by funext c; simp [w]
  have hw_univ : w Finset.univ = v := by funext c; simp [w]
  have hstep : ∀ (T : Finset (Fin (alg.arity index))) (c : Fin (alg.arity index)), c ∉ T →
      Relation.EqvGen (TranslateRel alg S) (alg.op index (w T))
        (alg.op index (w (insert c T))) := by
    intro T c hc
    have hwins : w (insert c T) = Function.update (w T) c (v c) := by
      funext d
      by_cases hd : d = c
      · subst hd; simp [w, Function.update_self]
      · simp [w, Finset.mem_insert, hd]
    rw [hwins]
    have hmem : w T c = if c ∈ T then v c else u c := rfl
    have hpoly : PolyCompatible alg (fun x : Carrier => alg.op index (Function.update (w T) c x)) :=
      coord_map_polyCompatible alg index (w T) c
    have := eqvGenTranslate_closed (S := S) hpoly (w T c) (v c) ?_
    · simpa [Function.update_self] using this
    · show Relation.EqvGen (TranslateRel alg S) (w T c) (v c)
      rw [hmem]
      rw [if_neg hc]
      exact huv c
  have hmain : ∀ T : Finset (Fin (alg.arity index)),
      Relation.EqvGen (TranslateRel alg S) (alg.op index u) (alg.op index (w T)) := by
    intro T
    induction T using Finset.induction with
    | empty => rw [hw_empty]; exact Relation.EqvGen.refl _
    | insert a s ha ih => exact Relation.EqvGen.trans _ _ _ ih (hstep s a ha)
  have := hmain Finset.univ
  rwa [hw_univ] at this
theorem eqvGenTranslate_compatible {Carrier : Type} (alg : Algebra Carrier)
    (S : Finset (Carrier × Carrier)) :
    Compatible alg (Relation.EqvGen.setoid (TranslateRel alg S)) := by
  intro index u v huv
  apply op_eqvGen_of_forall alg S index u v
  intro c
  exact huv c
theorem seed_mem_translateRel {Carrier : Type} {alg : Algebra Carrier}
    {S : Finset (Carrier × Carrier)} {p : Carrier × Carrier} (hp : p ∈ S) :
    TranslateRel alg S p.1 p.2 :=
  ⟨p, hp, id, fun _ _ _ huv => huv, rfl, rfl⟩
theorem congruence_mk_rel {Carrier : Type} {alg : Algebra Carrier}
    {rel : Setoid Carrier} {hc : Compatible alg rel} (a b : Carrier) :
    (⟨rel, hc⟩ : Congruence alg).1 a b ↔ rel a b := Iff.rfl
theorem poly_generated_eqvGen {Carrier : Type} (alg : Algebra Carrier)
    (S : Finset (Carrier × Carrier)) {a b : Carrier}
    (h : ∀ (θ : Congruence alg), (∀ p ∈ S, θ.1 p.1 p.2) → θ.1 a b) :
    Relation.EqvGen (TranslateRel alg S) a b := by
  classical
  have hrel := congruence_mk_rel (alg := alg)
    (rel := Relation.EqvGen.setoid (TranslateRel alg S))
    (hc := eqvGenTranslate_compatible alg S) a b
  refine hrel.mp ?_
  refine h ⟨Relation.EqvGen.setoid (TranslateRel alg S), eqvGenTranslate_compatible alg S⟩ ?_
  intro p hp
  have hp' := congruence_mk_rel (alg := alg)
    (rel := Relation.EqvGen.setoid (TranslateRel alg S))
    (hc := eqvGenTranslate_compatible alg S) p.1 p.2
  exact hp'.mpr (Relation.EqvGen.rel _ _ (seed_mem_translateRel (alg := alg) (S := S) hp))
abbrev witnessOpType {n : ℕ} {Lat : Type} [LE Lat]
    (color : Fin n → Fin n → Lat) : Type :=
  { f : Fin n → Fin n // Admissible color f }
noncomputable instance witnessOpTypeFintype {n : ℕ} {Lat : Type} [LE Lat]
    (color : Fin n → Fin n → Lat) : Fintype (witnessOpType color) :=
  Fintype.ofFinite _
noncomputable abbrev witnessAlgebra {n : ℕ} {Lat : Type} [LE Lat]
    (color : Fin n → Fin n → Lat) : Algebra (Fin n) where
  numOps := Fintype.card (witnessOpType color)
  arity := fun _ => 1
  op := fun index left =>
    ((Fintype.equivFin (witnessOpType color)).symm index : witnessOpType color).1 (left 0)
noncomputable def witnessRho {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (h : IsGraphWitness color) (a : Lat) :
    Congruence (witnessAlgebra color) := by
  classical
  refine ⟨⟨fun x y => color x y ≤ a, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro x
      have hxx : color x x = ⊥ := (h.2.1 x x).2 rfl
      rw [hxx]
      exact bot_le
    · intro x y hxy
      rwa [h.1 y x]
    · intro x y z hxy hyz
      calc
        color x z ≤ color x y ⊔ color y z := h.2.2.1 x z y
        _ ≤ a ⊔ a := sup_le (hxy.trans le_sup_left) (hyz.trans le_sup_right)
        _ = a := sup_idem a
  · intro index left right hcoord
    let e := Fintype.equivFin (witnessOpType color)
    let f : Fin n → Fin n := ((e.symm index : witnessOpType color)).1
    have hf : Admissible color f := (e.symm index).2
    change color (f (left 0)) (f (right 0)) ≤ a
    exact (hf (left 0) (right 0)).trans (hcoord 0)
lemma witnessAlgebra_admissible_apply {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    (f : Fin n → Fin n) (hf : Admissible color f) {u v : Fin n}
    (huv : θ.1 u v) : θ.1 (f u) (f v) := by
  classical
  let F : witnessOpType color := ⟨f, hf⟩
  let e := Fintype.equivFin (witnessOpType color)
  let index : Fin (witnessAlgebra color).numOps := e F
  have hleft : (witnessAlgebra color).op index
      (fun _ : Fin ((witnessAlgebra color).arity index) => u) = f u := by
    change ((e.symm index : witnessOpType color)).1 u = f u
    simp [index, e, F]
  have hright : (witnessAlgebra color).op index
      (fun _ : Fin ((witnessAlgebra color).arity index) => v) = f v := by
    change ((e.symm index : witnessOpType color)).1 v = f v
    simp [index, e, F]
  have h := θ.2 index (fun _ => u) (fun _ => v) (fun _ => huv)
  rwa [hleft, hright] at h
noncomputable def thetaSeeds {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color)) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter (fun edge => θ.1 edge.1 edge.2)
lemma thetaSeeds_mem {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    (edge : Fin n × Fin n) :
    edge ∈ thetaSeeds color θ ↔ θ.1 edge.1 edge.2 := by
  classical
  simp [thetaSeeds]
lemma thetaSeeds_nonempty {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    (hn : 0 < n) : (thetaSeeds color θ).Nonempty := by
  classical
  let x : Fin n := ⟨0, hn⟩
  refine ⟨(x, x), ?_⟩
  rw [thetaSeeds_mem]
lemma thetaSeeds_related {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    {edge : Fin n × Fin n} (h : edge ∈ thetaSeeds color θ) :
    θ.1 edge.1 edge.2 :=
  (thetaSeeds_mem color θ edge).1 h
lemma marked_mem_congruence {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    (seeds : Finset (Fin n × Fin n)) (hseed : ∀ edge ∈ seeds, θ.1 edge.1 edge.2)
    {left right : Fin n} (hm : Marked color seeds left right) : θ.1 left right := by
  classical
  rcases hm with ⟨placement, hadmissible, edge, hedge, hleft, hright⟩
  rw [← hleft, ← hright]
  exact witnessAlgebra_admissible_apply color θ placement hadmissible (hseed edge hedge)
lemma connected_mem_congruence {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color))
    (seeds : Finset (Fin n × Fin n)) (hseed : ∀ edge ∈ seeds, θ.1 edge.1 edge.2)
    {left right : Fin n} (hc : Connected color seeds left right) : θ.1 left right := by
  classical
  induction hc with
  | rel a b hab =>
      exact marked_mem_congruence color θ seeds hseed hab
  | refl x =>
      exact θ.1.refl' x
  | symm a b hab ih =>
      exact θ.1.symm' ih
  | trans a b c hab hbc ihab ihbc =>
      exact θ.1.trans' ihab ihbc
noncomputable def witnessRhoSup {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (θ : Congruence (witnessAlgebra color)) : Lat :=
  (thetaSeeds color θ).sup (fun edge => color edge.1 edge.2)
lemma mem_iff_rho_thetaSeeds {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (h : IsGraphWitness color)
    (θ : Congruence (witnessAlgebra color)) (hn : 0 < n) (left right : Fin n) :
    θ.1 left right ↔
      color left right ≤ (thetaSeeds color θ).sup (fun edge => color edge.1 edge.2) := by
  classical
  constructor
  · intro hrel
    exact Finset.le_sup (s := thetaSeeds color θ)
      (f := fun edge : Fin n × Fin n => color edge.1 edge.2) (b := (left, right))
      ((thetaSeeds_mem color θ (left, right)).2 hrel)
  · intro hcolor
    exact connected_mem_congruence color θ (thetaSeeds color θ)
      (fun edge hedge => thetaSeeds_related color θ hedge)
      (h.2.2.2.2 (thetaSeeds color θ) (thetaSeeds_nonempty color θ hn) left right hcolor)
lemma witnessRho_surjective {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (h : IsGraphWitness color) (hn : 0 < n) :
    Function.Surjective (witnessRho color h) := by
  classical
  intro θ
  refine ⟨witnessRhoSup color θ, ?_⟩
  apply Subtype.ext
  apply Setoid.ext
  intro left right
  exact (mem_iff_rho_thetaSeeds color h θ hn left right).symm
noncomputable def witnessEmbedding {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (h : IsGraphWitness color) :
    Lat ↪o Congruence (witnessAlgebra color) :=
  OrderEmbedding.ofMapLEIff (witnessRho color h) (by
    intro a b
    constructor
    · intro hle
      by_contra hnot
      rcases h.2.2.2.1 a b hnot with ⟨left, right, hleft, hright⟩
      exact hright (hle hleft)
    · intro hle left right hleft
      exact hleft.trans hle)
noncomputable def witnessOrderIso {n : ℕ} {Lat : Type} [Lattice Lat] [OrderBot Lat]
    (color : Fin n → Fin n → Lat) (h : IsGraphWitness color) (hn : 0 < n) :
    Lat ≃o Congruence (witnessAlgebra color) :=
  OrderIso.ofSurjective (witnessEmbedding color h) (witnessRho_surjective color h hn)
theorem witness_representable (n : ℕ) (hn : 0 < n) :
    ∀ {Lat : Type} [Fintype Lat] [Lattice Lat] [OrderBot Lat]
      (color : Fin n → Fin n → Lat), IsGraphWitness color → Representable Lat := by
  intro Lat _ _ _ color h
  exact ⟨n, hn, witnessAlgebra color, ⟨witnessOrderIso color h hn⟩⟩
theorem principal_isGraphWitness (n : ℕ) (_hn : 0 < n) {Lat : Type} [Fintype Lat]
    [Lattice Lat] [OrderBot Lat]
    (alg : Algebra (Fin n)) (e : Lat ≃o Congruence alg) :
    IsGraphWitness (fun x y : Fin n => e.symm (Principal alg x y)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp
    rw [Principal_comm]
  · intro x y
    dsimp
    have hbot : e (⊥ : Lat) = (⊥ : Congruence alg) := by
      apply le_antisymm
      · have h : (⊥ : Lat) ≤ e.symm (⊥ : Congruence alg) := bot_le
        have h' : e (⊥ : Lat) ≤ e (e.symm (⊥ : Congruence alg)) :=
          (e.le_iff_le).mpr h
        simpa using h'
      · change Principal_diagonal alg ≤ e (⊥ : Lat)
        exact Principal_diagonal_le alg (e (⊥ : Lat))
    constructor
    · intro h
      have h' : Principal alg x y = e (⊥ : Lat) := by
        have := congrArg e h
        simpa using this
      have h'' : Principal alg x y = (⊥ : Congruence alg) := by
        simpa [hbot] using h'
      exact (principal_bot_iff alg x y).1 h''
    · intro h
      have h' : Principal alg x y = (⊥ : Congruence alg) := (principal_bot_iff alg x y).2 h
      have h'' : Principal alg x y = e (⊥ : Lat) := by
        simpa [hbot] using h'
      have := congrArg e.symm h''
      simpa using this
  · intro x y z
    dsimp
    let a : Lat := e.symm (Principal alg x z)
    let b : Lat := e.symm (Principal alg z y)
    let θ : Congruence alg := e (a ⊔ b)
    have hxz : θ.1 x z := by
      have hle : Principal alg x z ≤ θ := by
        have h := (e.le_iff_le).mpr (le_sup_left : a ≤ a ⊔ b)
        simpa [θ, a] using h
      exact (Principal_le_iff alg x z θ).1 hle
    have hzy : θ.1 z y := by
      have hle : Principal alg z y ≤ θ := by
        have h := (e.le_iff_le).mpr (le_sup_right : b ≤ a ⊔ b)
        simpa [θ, b] using h
      exact (Principal_le_iff alg z y θ).1 hle
    have hxy : Principal alg x y ≤ θ := Principal_trans_le alg θ hxz hzy
    have h' : e (e.symm (Principal alg x y)) ≤ e (a ⊔ b) := by
      simpa [θ] using hxy
    have h'' := (e.le_iff_le).mp h'
    simpa [a, b] using h''
  · intro lower upper hnot
    have hnot' : ¬ e lower ≤ e upper := by
      intro h
      exact hnot ((e.le_iff_le).mp h)
    have hnotrel : ¬ (e lower).1 ≤ (e upper).1 := by
      change ¬ e lower ≤ e upper
      exact hnot'
    have hex : ∃ a b, (e lower).1 a b ∧ ¬ (e upper).1 a b := by
      by_contra h
      apply hnotrel
      rw [Setoid.le_def]
      intro a b hab
      by_contra hnab
      exact h ⟨a, b, hab, hnab⟩
    rcases hex with ⟨a, b, hab_lower, hab_not_upper⟩
    refine ⟨a, b, ?_, ?_⟩
    · have hP : Principal alg a b ≤ e lower :=
        (Principal_le_iff alg a b (e lower)).2 hab_lower
      simpa using e.symm.monotone hP
    · intro hle
      have hP : Principal alg a b ≤ e upper := by
        have h := e.monotone hle
        simpa using h
      exact hab_not_upper ((Principal_le_iff alg a b (e upper)).1 hP)
  · intro seeds _hseeds x y hxy
    change Relation.EqvGen (Marked (fun x y : Fin n => e.symm (Principal alg x y)) seeds) x y
    have hgen : Relation.EqvGen (TranslateRel alg seeds) x y := by
      refine poly_generated_eqvGen alg seeds ?_
      intro θ hθ
      let T : Lat := seeds.sup (fun edge => e.symm (Principal alg edge.1 edge.2))
      have hTle : T ≤ e.symm θ := by
        apply Finset.sup_le
        intro edge hedge
        have hP : Principal alg edge.1 edge.2 ≤ θ :=
          (Principal_le_iff alg edge.1 edge.2 θ).2 (hθ edge hedge)
        exact e.symm.monotone hP
      have heT : e T ≤ θ := by
        have h := e.monotone hTle
        simpa using h
      have hPxy : Principal alg x y ≤ e T := by
        have h := e.monotone hxy
        simpa [T] using h
      exact (Principal_le_iff alg x y θ).1 (le_trans hPxy heT)
    have hsubset : TranslateRel alg seeds ≤
        Marked (fun x y : Fin n => e.symm (Principal alg x y)) seeds := by
      intro u v huv
      rcases huv with ⟨p, hp, f, hf, rfl, rfl⟩
      refine ⟨f, ?_, p, hp, rfl, rfl⟩
      intro left right
      have hP : Principal alg (f left) (f right) ≤ Principal alg left right :=
        (Principal_le_iff alg (f left) (f right) (Principal alg left right)).2
          (hf (Principal alg left right) left right (Principal_mem_self alg left right))
      exact e.symm.monotone hP
    exact Relation.EqvGen.mono hsubset x y hgen
theorem representable_witness {Lat : Type} [Fintype Lat] [Lattice Lat] [OrderBot Lat]
    (h : Representable Lat) : HasGraphWitness Lat := by
  rcases h with ⟨n, hn, alg, ⟨e⟩⟩
  exact ⟨n, hn, (fun x y : Fin n => e.symm (Principal alg x y)),
    principal_isGraphWitness n hn alg e⟩
theorem graph_criterion_from_directions (Lat : Type)
    [Fintype Lat] [Lattice Lat] [OrderBot Lat] :
    Representable Lat ↔ HasGraphWitness Lat := by
  constructor
  · exact representable_witness
  · intro h
    rcases h with ⟨n, hn, color, hcolor⟩
    exact witness_representable n hn color hcolor
/-- A finite lattice is representable as the full congruence lattice of a nonempty finite
algebra exactly when it has a finite nonempty colored-graph witness. -/
theorem graph_criterion (Lat : Type) [Fintype Lat] [Lattice Lat] [OrderBot Lat] :
    Representable Lat ↔ HasGraphWitness Lat := by
  exact graph_criterion_from_directions Lat
end FiniteCongruence

end OAI
