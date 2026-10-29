module
public import DeterminationPatterns.Core
@[expose] public section

namespace DeterminationPatterns
universe u

/-- Classical truth-value representation; unlike a computable decision procedure,
this encodes arbitrary propositions. -/
noncomputable def boolOf (p : Prop) : Bool := by
  classical
  exact if p then true else false

def propOf (b : Bool) : Prop := b = true

@[simp] theorem propOf_boolOf (p : Prop) : propOf (boolOf p) ↔ p := by
  classical
  simp [propOf, boolOf]

@[simp] theorem boolOf_propOf (b : Bool) : boolOf (propOf b) = b := by
  cases b <;> simp [propOf, boolOf]

noncomputable def boolRegion {α : Type u} (S : Region α) : α → Bool :=
  fun x => boolOf (S x)

def propRegion {α : Type u} (S : α → Bool) : Region α := fun x => propOf (S x)

@[simp] theorem prop_bool_region {α : Type u} (S : Region α) :
    propRegion (boolRegion S) = S := by
  funext x
  exact propext (propOf_boolOf (S x))

@[simp] theorem bool_prop_region {α : Type u} (S : α → Bool) :
    boolRegion (propRegion S) = S := by
  funext x
  exact boolOf_propOf (S x)

noncomputable def boolRelation {α : Type u} (D : α → α → Prop) : α → α → Bool :=
  fun x y => boolOf (D x y)

def propRelation {α : Type u} (D : α → α → Bool) : α → α → Prop :=
  fun x y => propOf (D x y)

@[simp] theorem prop_bool_relation {α : Type u} (D : α → α → Prop) :
    propRelation (boolRelation D) = D := by
  funext x y
  exact propext (propOf_boolOf (D x y))

@[simp] theorem bool_prop_relation {α : Type u} (D : α → α → Bool) :
    boolRelation (propRelation D) = D := by
  funext x y
  exact boolOf_propOf (D x y)

/-- HOL-style Boolean mechanism on the full powerset of the carrier type. -/
noncomputable def boolMechanism {α : Type u} (f : α → Region α → Prop) :
    α → Region α → Bool := fun x S => boolOf (f x S)

def propMechanism {α : Type u} (f : α → Region α → Bool) :
    α → Region α → Prop := fun x S => propOf (f x S)

@[simp] theorem prop_bool_mechanism {α : Type u} (f : α → Region α → Prop) :
    propMechanism (boolMechanism f) = f := by
  funext x S
  exact propext (propOf_boolOf (f x S))

@[simp] theorem bool_prop_mechanism {α : Type u} (f : α → Region α → Bool) :
    boolMechanism (propMechanism f) = f := by
  funext x S
  exact boolOf_propOf (f x S)

theorem boolean_model_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) :
    Mechanism (propRegion (boolRegion C)) (propRelation (boolRelation D))
        (propMechanism (boolMechanism f)) ↔ Mechanism C D f := by simp

theorem boolean_relevance_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) :
    Relevant (propRegion (boolRegion C)) (propRelation (boolRelation D))
        (propMechanism (boolMechanism f)) ↔ Relevant C D f := by simp

theorem boolean_step_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U X : Region α) :
    Step (propRegion (boolRegion C)) (propRelation (boolRelation D))
      (propMechanism (boolMechanism f)) (propRegion (boolRegion U))
      (propRegion (boolRegion X)) = Step C D f U X := by simp

/-- Least and greatest are respectively the intersection of pre-fixed sets and
union of post-fixed sets. Their fixedness is proved in Core for monotone maps. -/
theorem least_iff_below_all_fixed {α : Type u} {F : Region α → Region α}
    (hF : Monotone F) (x : α) :
    Least F x ↔ ∀ X, Fixed F X → X x := by
  constructor
  · intro hl X hX
    exact (fixed_bounds hX).1 hl
  · intro h
    exact h (Least F) (least_fixed hF)

theorem greatest_iff_below_some_fixed {α : Type u} {F : Region α → Region α}
    (hF : Monotone F) (x : α) :
    Greatest F x ↔ ∃ X, Fixed F X ∧ X x := by
  constructor
  · intro hg
    exact ⟨Greatest F, greatest_fixed hF, hg⟩
  · rintro ⟨X, hX, hx⟩
    exact (fixed_bounds hX).2 hx

theorem empty_vertex_regions_equal {α : Type u} (empty : ∀ _ : α, False) (X Y : Region α) : X = Y := by
  funext x
  exact False.elim (empty x)

/-- Every nonempty subset of X receives an input from outside itself relative
 to X. -/
def Supported {α : Type u} (F : Region α → Region α) (X : Region α) : Prop :=
  ∀ S : Region α, Sub S X → (∃ x, S x) →
    ∃ x, S x ∧ F (fun y => X y ∧ ¬ S y) x

/-- The Isabelle `grounded_fixed_iff_least` condition for a monotone powerset map. -/
theorem supported_fixed_iff_least {α : Type u} {F : Region α → Region α}
    (hm : Monotone F) {X : Region α} (hX : Fixed F X) :
    Supported F X ↔ X = Least F := by
  classical
  have low : Sub (Least F) X := (fixed_bounds hX).1
  have leastFix : Fixed F (Least F) := least_fixed hm
  constructor
  · intro hs
    apply funext
    intro x
    apply propext
    constructor
    · intro hx
      apply Classical.byContradiction; intro hn
      let S : Region α := fun y => X y ∧ ¬ Least F y
      have ssub : Sub S X := by intro y hy; exact hy.1
      obtain ⟨y, ⟨hyX, hyNot⟩, hFy⟩ := hs S ssub ⟨x, hx, hn⟩
      have remain : Sub (fun y => X y ∧ ¬ S y) (Least F) := by
        intro z hz
        apply Classical.byContradiction; intro hzNot
        exact hz.2 ⟨hz.1, hzNot⟩
      have hlow : F (Least F) y := hm _ _ remain hFy
      rw [leastFix] at hlow
      exact hyNot hlow
    · intro hl; exact low hl
  · intro hEq S hSX hS
    obtain ⟨x, hx⟩ := hS
    apply Classical.byContradiction; intro hNone
    have pre : Sub (F (fun y => X y ∧ ¬ S y)) (fun y => X y ∧ ¬ S y) := by
      intro y hy
      have hxy : X y := by
        have hsub : Sub (fun y => X y ∧ ¬ S y) X := by intro z hz; exact hz.1
        have hf : F X y := hm _ _ hsub hy
        rw [hX] at hf
        exact hf
      have hn : ¬ S y := by
        intro hsy
        exact hNone ⟨y, hsy, hy⟩
      exact ⟨hxy, hn⟩
    have hxLeast : Least F x := by rw [← hEq]; exact hSX hx
    have hxNot : ¬ S x := (least_le F _ pre hxLeast).2
    exact hxNot hx

/-- A Boolean mechanism accepts Boolean-coded arbitrary regions, as in HOL. -/
noncomputable def toBooleanMechanism {α : Type u} (f : α → Region α → Prop) :
    α → (α → Bool) → Bool := fun x S => boolOf (f x (propRegion S))

noncomputable def fromBooleanMechanism {α : Type u} (f : α → (α → Bool) → Bool) :
    α → Region α → Prop := fun x S => propOf (f x (boolRegion S))

@[simp] theorem from_to_boolean_mechanism {α : Type u} (f : α → Region α → Prop) :
    fromBooleanMechanism (toBooleanMechanism f) = f := by
  funext x S
  simp [fromBooleanMechanism, toBooleanMechanism]

@[simp] theorem to_from_boolean_mechanism {α : Type u} (f : α → (α → Bool) → Bool) :
    toBooleanMechanism (fromBooleanMechanism f) = f := by
  funext x S
  simp [fromBooleanMechanism, toBooleanMechanism]

theorem boolean_input_model_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) :
    Mechanism (propRegion (boolRegion C)) (propRelation (boolRelation D))
        (fromBooleanMechanism (toBooleanMechanism f)) ↔ Mechanism C D f := by simp

theorem boolean_input_relevance_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) :
    Relevant (propRegion (boolRegion C)) (propRelation (boolRelation D))
        (fromBooleanMechanism (toBooleanMechanism f)) ↔ Relevant C D f := by simp

theorem boolean_input_step_roundtrip {α : Type u} (C : Region α) (D : α → α → Prop)
    (f : α → Region α → Prop) (U X : Region α) :
    Step (propRegion (boolRegion C)) (propRelation (boolRelation D))
      (fromBooleanMechanism (toBooleanMechanism f)) (propRegion (boolRegion U))
      (propRegion (boolRegion X)) = Step C D f U X := by simp

theorem contextual_grounded_fixed_iff_least {α : Type u} {C : Region α}
    {D : α → α → Prop} {f : α → Region α → Prop} {U X : Region α}
    (h : Mechanism C D f) (_hU : Sub U (Roots C D))
    (hX : Fixed (Step C D f U) X) :
    Supported (Step C D f U) X ↔ X = Least (Step C D f U) :=
  supported_fixed_iff_least (step_monotone h U) hX

end DeterminationPatterns
