module
public import DeterminationPatterns.LabelledSpine
@[expose] public section

namespace DeterminationPatterns
universe u

/-- A normalized two-input rule is AND, OR, or one of the two projections.
The conclusion concerns parent-restricted inputs, so the rule's values on
sets containing other vertices are immaterial. The four-case conclusion
already follows from normalization, without a monotonicity assumption. -/
theorem normalized_two_input_four_cases {β : Type u} (p q : β) (f : Region β → Prop)
    (_neq : p ≠ q) (zero : ¬ f (fun _ => False))
    (one : f (fun z => z = p ∨ z = q)) :
    (∀ X : Region β, f (fun z => X z ∧ (z = p ∨ z = q)) ↔ X p ∧ X q) ∨
    (∀ X : Region β, f (fun z => X z ∧ (z = p ∨ z = q)) ↔ X p ∨ X q) ∨
    (∀ X : Region β, f (fun z => X z ∧ (z = p ∨ z = q)) ↔ X p) ∨
    (∀ X : Region β, f (fun z => X z ∧ (z = p ∨ z = q)) ↔ X q) := by
  classical
  have table (X : Region β) :
      f (fun z => X z ∧ (z = p ∨ z = q)) ↔
        (X p ∧ X q) ∨ (X p ∧ f (fun z => z = p)) ∨
          (X q ∧ f (fun z => z = q)) := by
    by_cases hp : X p <;> by_cases hq : X q
    · have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = p ∨ z = q) := by
        funext z
        apply propext
        constructor
        · exact fun h => h.2
        · intro h
          rcases h with rfl | rfl <;> simp [hp, hq]
      rw [eq]
      simp [hp, hq, one]
    · have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = p) := by
        funext z
        apply propext
        constructor
        · rintro ⟨_, hz | hz⟩
          · exact hz
          · subst z
            exact False.elim (hq ‹X q›)
        · intro hz
          subst z
          exact ⟨hp, Or.inl rfl⟩
      rw [eq]
      simp [hp, hq]
    · have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun z => z = q) := by
        funext z
        apply propext
        constructor
        · rintro ⟨_, hz | hz⟩
          · subst z
            exact False.elim (hp ‹X p›)
          · exact hz
        · intro hz
          subst z
          exact ⟨hq, Or.inr rfl⟩
      rw [eq]
      simp [hp, hq]
    · have eq : (fun z => X z ∧ (z = p ∨ z = q)) = (fun _ => False) := by
        funext z
        apply propext
        constructor
        · rintro ⟨hzX, hz | hz⟩
          · subst z
            exact hp hzX
          · subst z
            exact hq hzX
        · exact fun h => False.elim h
      rw [eq]
      simp [hp, hq, zero]
  by_cases hp : f (fun z => z = p) <;> by_cases hq : f (fun z => z = q)
  · right; left
    intro X
    by_cases xp : X p <;> by_cases xq : X q <;> simpa [hp, hq, xp, xq] using table X
  · right; right; left
    intro X
    by_cases xp : X p <;> by_cases xq : X q <;> simpa [hp, hq, xp, xq] using table X
  · right; right; right
    intro X
    by_cases xp : X p <;> by_cases xq : X q <;> simpa [hp, hq, xp, xq] using table X
  · left
    intro X
    simpa [hp, hq] using table X

/-- The four explicit Boolean gates for distinct ordered inputs. -/
def twoInputAnd (a b : Bool) : Bool := a && b
def twoInputOr (a b : Bool) : Bool := a || b
def twoInputFirst (a _b : Bool) : Bool := a
def twoInputSecond (_a b : Bool) : Bool := b

def BooleanGateNormalized (f : Bool → Bool → Bool) : Prop :=
  f false false = false ∧ f true true = true

def BooleanGateMonotone (f : Bool → Bool → Bool) : Prop :=
  ∀ a a' b b' : Bool, (a = true → a' = true) → (b = true → b' = true) →
    f a b = true → f a' b' = true

theorem four_boolean_gates_are_normalized_and_monotone :
    BooleanGateNormalized twoInputAnd ∧ BooleanGateMonotone twoInputAnd ∧
    BooleanGateNormalized twoInputOr ∧ BooleanGateMonotone twoInputOr ∧
    BooleanGateNormalized twoInputFirst ∧ BooleanGateMonotone twoInputFirst ∧
    BooleanGateNormalized twoInputSecond ∧ BooleanGateMonotone twoInputSecond := by
  simp [BooleanGateNormalized, BooleanGateMonotone, Bool.forall_bool,
    twoInputAnd, twoInputOr, twoInputFirst, twoInputSecond]

/-- The gates are pairwise distinct, witnessed by the two singleton inputs. -/
theorem four_boolean_gates_are_distinct :
    twoInputAnd true false ≠ twoInputOr true false ∧
    twoInputAnd true false ≠ twoInputFirst true false ∧
    twoInputAnd false true ≠ twoInputSecond false true ∧
    twoInputOr false true ≠ twoInputFirst false true ∧
    twoInputOr true false ≠ twoInputSecond true false ∧
    twoInputFirst true false ≠ twoInputSecond true false := by
  decide

/-- The four Boolean gates act as the four predicate gates on the same inputs. -/
theorem boolean_four_gates_match_predicates {β : Type u} (p q : β) (S : Region β) :
    (twoInputAnd (boolOf (S p)) (boolOf (S q)) = true ↔ S p ∧ S q) ∧
    (twoInputOr (boolOf (S p)) (boolOf (S q)) = true ↔ S p ∨ S q) ∧
    (twoInputFirst (boolOf (S p)) (boolOf (S q)) = true ↔ S p) ∧
    (twoInputSecond (boolOf (S p)) (boolOf (S q)) = true ↔ S q) := by
  classical
  by_cases hp : S p <;> by_cases hq : S q <;>
    simp [twoInputAnd, twoInputOr, twoInputFirst, twoInputSecond, boolOf, hp, hq]

end DeterminationPatterns
