module
public import DeterminationPatterns.LabelledSpine
@[expose] public section

namespace DeterminationPatterns

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
