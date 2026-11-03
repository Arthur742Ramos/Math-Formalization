/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineSuccessor
public meta import LambdaTuring.MachineSuccessor
public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom

@[expose] public section

namespace LambdaTuring.Machine

/-- Rewriting the input symbol forever gives an actual nonhalting finite machine. -/
def loopMachine : Program 0 := ⟨[none, some (⟨0, by decide⟩, .write .one)]⟩

theorem loopMachine_step (n : Nat) : step loopMachine (initial n) = some (initial n) := by
  rfl

theorem loopMachine_reaches (n : Nat) {c : Config 0} (h : Reaches loopMachine (initial n) c) :
    c = initial n := by
  have hstar : ∀ {a b : Config 0}, Reaches loopMachine a b → a = initial n → b = initial n := by
    intro a b hr
    induction hr with
    | refl => exact fun ha => ha
    | step hs _ ih =>
      intro ha
      cases ha
      rw [loopMachine_step] at hs
      have hb := Option.some.inj hs
      exact ih hb.symm
  exact hstar h rfl

theorem loopMachine_no_yields (n m : Nat) : ¬ Yields loopMachine n m := by
  rintro ⟨c, hc, hh, _⟩
  have heq := loopMachine_reaches n hc
  subst c
  change step loopMachine (initial n) = none at hh
  rw [loopMachine_step] at hh
  cases hh

theorem loopMachine_value (n : Nat) : machineValue loopMachine n = Part.none := by
  apply (machineValue_none_iff loopMachine n).2
  exact loopMachine_no_yields n

/-- Extend the finite-table compiler with one concrete undefined code. -/
def compileWithBottomMachine (c : Nat.Partrec.Code) : Option (Σ states, Program states) :=
  if Encodable.encode c = Encodable.encode bottomCode then some ⟨0, loopMachine⟩
  else compileSuccessorMachine c

theorem compileWithBottomMachine_bottom :
    compileWithBottomMachine bottomCode = some ⟨0, loopMachine⟩ := by
  simp [compileWithBottomMachine]

theorem compileWithBottomMachine_sound (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileWithBottomMachine c = some p) (n : Nat) :
    machineValue p.2 n = Nat.Partrec.Code.eval c n := by
  by_cases hb : Encodable.encode c = Encodable.encode bottomCode
  · have hp : (⟨0, loopMachine⟩ : Σ states, Program states) = p := by
      simpa [compileWithBottomMachine, hb] using h
    have hc : c = bottomCode := Encodable.encode_injective hb
    subst p
    subst c
    rw [bottomCode_eval]
    exact loopMachine_value n
  · exact compileSuccessorMachine_sound c p (by simpa [compileWithBottomMachine, hb] using h) n

theorem compileWithBottomMachine_mathYields (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileWithBottomMachine c = some p) (n m : Nat) :
    MathYields p.2 n m ↔ m ∈ Nat.Partrec.Code.eval c n := by
  rw [math_yields_iff, ← mem_machineValue_iff, compileWithBottomMachine_sound c p h n]

theorem compileWithBottomMachine_mathNone (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileWithBottomMachine c = some p) (n : Nat) :
    (∀ m, ¬ MathYields p.2 n m) ↔ Nat.Partrec.Code.eval c n = Part.none := by
  rw [math_no_numerical_iff, ← machineValue_none_iff, compileWithBottomMachine_sound c p h n]

#print axioms loopMachine_no_yields
#print axioms compileWithBottomMachine_mathYields
#print axioms compileWithBottomMachine_mathNone

end LambdaTuring.Machine
