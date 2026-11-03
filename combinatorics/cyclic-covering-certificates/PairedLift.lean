module
/-
The combinatorial implication in paired quadratic lifting, abstracted from the
field arithmetic.  The coordinate maps, their character compatibility, and the
two permutation selections are explicit hypotheses.  No finite-field character
estimate or existence theorem is assumed as an undeclared axiom.
-/
public import Std
public section

namespace CoveringPairedLift

structure LiftData (R X G Y : Type) where
  first : R → Bool → G
  coordinate : R → X → Y
  label : R → Bool
  character : X → Bool
  targetCharacter : Y → Bool
  coordinateUnique : ∀ r y, ∃ x, coordinate r x = y ∧
    ∀ x', coordinate r x' = y → x' = x
  selectorUnique : ∀ L g, ∃ r, first r (Bool.xor L (label r)) = g ∧
    ∀ r', first r' (Bool.xor L (label r')) = g → r' = r
  characterRule : ∀ r x,
    character x = Bool.xor (targetCharacter (coordinate r x)) (label r)

@[expose] def lifted {R X G Y : Type} (data : LiftData R X G Y) (input : R × X) : G × Y :=
  (data.first input.1 (data.character input.2), data.coordinate input.1 input.2)

/-- Each target outside the hole has exactly one preimage in the paired lift. -/
theorem pairedLiftUnique {R X G Y : Type} (data : LiftData R X G Y) (g : G) (y : Y) :
    ∃ r x, data.first r (data.character x) = g ∧ data.coordinate r x = y ∧
      ∀ r' x', data.first r' (data.character x') = g → data.coordinate r' x' = y →
        r' = r ∧ x' = x := by
  obtain ⟨r, hr, hrUnique⟩ := data.selectorUnique (data.targetCharacter y) g
  obtain ⟨x, hx, hxUnique⟩ := data.coordinateUnique r y
  have hsign : data.character x = Bool.xor (data.targetCharacter y) (data.label r) := by
    rw [data.characterRule r x, hx]
  have hfirst : data.first r (data.character x) = g := by
    rw [hsign]
    exact hr
  refine ⟨r, x, hfirst, hx, ?_⟩
  intro r' x' hfirst' hx'
  have hsign' : data.character x' = Bool.xor (data.targetCharacter y) (data.label r') := by
    rw [data.characterRule r' x', hx']
  have hselected : data.first r' (Bool.xor (data.targetCharacter y) (data.label r')) = g := by
    rw [← hsign']
    exact hfirst'
  have heq : r' = r := hrUnique r' hselected
  subst r'
  exact ⟨rfl, hxUnique x' hx'⟩

/-- Surjectivity and injectivity together, stated without additional libraries. -/
theorem pairedLiftBijection {R X G Y : Type} (data : LiftData R X G Y) :
    (∀ target : G × Y, ∃ input, lifted data input = target) ∧
    (∀ a b : R × X, lifted data a = lifted data b → a = b) := by
  constructor
  · intro target
    obtain ⟨r, x, hfirst, hx, _⟩ := pairedLiftUnique data target.1 target.2
    refine ⟨(r,x), ?_⟩
    apply Prod.ext
    · exact hfirst
    · exact hx
  · intro a b hab
    obtain ⟨r, x, _, _, hUnique⟩ := pairedLiftUnique data
      (data.first a.1 (data.character a.2)) (data.coordinate a.1 a.2)
    have ha := hUnique a.1 a.2 rfl rfl
    have hb := hUnique b.1 b.2 (congrArg Prod.fst hab).symm (congrArg Prod.snd hab).symm
    apply Prod.ext
    · exact ha.1.trans hb.1.symm
    · exact ha.2.trans hb.2.symm

#print axioms pairedLiftUnique
#print axioms pairedLiftBijection

end CoveringPairedLift
