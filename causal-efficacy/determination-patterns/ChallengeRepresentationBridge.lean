module
import Init
@[expose] public section

/-! Boolean/Prop gate correspondence and successor indexing. -/
namespace DeterminationPatterns

/-- OR if the gate bit is true, AND if it is false. -/
def SpineGate (g b : Bool) (z : Prop) : Prop :=
  if g then (b = true ∨ z) else (b = true ∧ z)


/-- Boolean analogue of the source gate equation: true selects OR. -/
def IsabelleGateEquation (g b z : Bool) : Bool :=
  if g then b || z else b && z

/-- The mixed Bool/Prop gate agrees with that Boolean equation when the
    proposition represents the truth of the third Boolean input. -/
theorem spine_gate_boolean_equation (g b z : Bool) :
    SpineGate g b (z = true) ↔ IsabelleGateEquation g b z = true := by
  cases g <;> cases b <;> cases z <;> simp [SpineGate, IsabelleGateEquation]

theorem spine_gate_false_false (z : Prop) : ¬ SpineGate false false z := by
  simp [SpineGate]

theorem spine_gate_false_true (z : Prop) : SpineGate false true z ↔ z := by
  simp [SpineGate]

theorem spine_gate_true_false (z : Prop) : SpineGate true false z ↔ z := by
  simp [SpineGate]

theorem spine_gate_true_true (z : Prop) : SpineGate true true z := by
  simp [SpineGate]

theorem index_successor (n : Nat) : n + 1 = Nat.succ n := by
  simp

end DeterminationPatterns
