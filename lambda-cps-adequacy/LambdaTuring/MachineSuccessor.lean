/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineCompilerBase
public meta import LambdaTuring.MachineCompilerBase

@[expose] public section

namespace LambdaTuring.Machine

/-- Append one unary symbol, then return to the left end of the output. -/
def successorMachine : Program 2 :=
  ⟨[some (⟨1, by decide⟩, .write .one), some (⟨0, by decide⟩, .right), none,
    some (⟨2, by decide⟩, .right), some (⟨1, by decide⟩, .left)]⟩

def successorScan (written remaining : Nat) : Config 2 :=
  ⟨⟨0, by decide⟩, ⟨List.replicate written .one, .one, List.replicate remaining .one⟩⟩
def successorBlank (written : Nat) : Config 2 :=
  ⟨⟨0, by decide⟩, ⟨List.replicate written .one, .blank, []⟩⟩
def successorReturn (left right : Nat) : Config 2 :=
  ⟨⟨1, by decide⟩, ⟨List.replicate left .one, .one, List.replicate right .one⟩⟩
def successorReturnBlank (right : Nat) : Config 2 :=
  ⟨⟨1, by decide⟩, ⟨[], .blank, List.replicate right .one⟩⟩
def successorHalt (right : Nat) : Config 2 :=
  ⟨⟨2, by decide⟩, ⟨[.blank], .one, List.replicate right .one⟩⟩

theorem successorScan_next (written remaining : Nat) :
    step successorMachine (successorScan written (remaining + 1)) =
      some (successorScan (written + 1) remaining) := by
  simp [successorMachine, successorScan, step, instruction, symbolIndex, perform, moveRight, List.replicate_succ]

theorem successorScan_last (written : Nat) :
    step successorMachine (successorScan written 0) = some (successorBlank (written + 1)) := by
  simp [successorMachine, successorScan, successorBlank, step, instruction, symbolIndex,
    perform, moveRight, List.replicate_succ]

theorem successorScan_reaches (written remaining : Nat) :
    Reaches successorMachine (successorScan written remaining) (successorBlank (written + remaining + 1)) := by
  induction remaining generalizing written with
  | zero => simpa using Reaches.step (successorScan_last written) (Reaches.refl _)
  | succ remaining ih =>
    have h := Reaches.step (successorScan_next written remaining) (ih (written + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem successorBlank_next (written : Nat) :
    step successorMachine (successorBlank written) = some (successorReturn written 0) := by
  rfl

theorem successorReturn_next (left right : Nat) :
    step successorMachine (successorReturn (left + 1) right) = some (successorReturn left (right + 1)) := by
  simp [successorMachine, successorReturn, step, instruction, symbolIndex, perform, moveLeft, List.replicate_succ]

theorem successorReturn_last (right : Nat) :
    step successorMachine (successorReturn 0 right) = some (successorReturnBlank (right + 1)) := by
  simp [successorMachine, successorReturn, successorReturnBlank, step, instruction, symbolIndex,
    perform, moveLeft, List.replicate_succ]

theorem successorReturn_reaches (left right : Nat) :
    Reaches successorMachine (successorReturn left right) (successorReturnBlank (left + right + 1)) := by
  induction left generalizing right with
  | zero => simpa using Reaches.step (successorReturn_last right) (Reaches.refl _)
  | succ left ih =>
    have h := Reaches.step (successorReturn_next left right) (ih (right + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem successorReturnBlank_next (right : Nat) :
    step successorMachine (successorReturnBlank (right + 1)) = some (successorHalt right) := by
  simp [successorMachine, successorReturnBlank, successorHalt, step, instruction, symbolIndex,
    perform, moveRight, List.replicate_succ]

theorem successorHalt_halted (right : Nat) : Halted successorMachine (successorHalt right) := by
  rfl

theorem successorMachine_yields (n : Nat) : Yields successorMachine n (n + 1) := by
  refine ⟨successorHalt (n + 1), ?_, successorHalt_halted _, ?_⟩
  · apply reaches_trans (b := successorBlank (n + 1))
    · simpa [successorScan, initial] using successorScan_reaches 0 n
    · apply reaches_trans (b := successorReturn (n + 1) 0)
      · exact .step (successorBlank_next _) (.refl _)
      · apply reaches_trans (b := successorReturnBlank (n + 1 + 1))
        · simpa using successorReturn_reaches (n + 1) 0
        · exact .step (successorReturnBlank_next _) (.refl _)
  · simpa [successorHalt, input, List.replicate_succ] using decode_input (n + 1)

theorem successorMachine_yields_iff (n m : Nat) : Yields successorMachine n m ↔ m = n + 1 := by
  constructor
  · intro h
    exact yields_unique h (successorMachine_yields n)
  · intro h
    subst m
    exact successorMachine_yields n

theorem successorMachine_value (n : Nat) : machineValue successorMachine n = Part.some (n + 1) := by
  apply Part.ext
  intro m
  rw [mem_machineValue_iff, successorMachine_yields_iff]
  simp

theorem successorMachine_mathYields (n m : Nat) :
    MathYields successorMachine n m ↔ m ∈ Nat.Partrec.Code.eval .succ n := by
  rw [math_yields_iff, ← mem_machineValue_iff, successorMachine_value]
  rfl

theorem successorMachine_mathNone (n : Nat) :
    (∀ m, ¬ MathYields successorMachine n m) ↔ Nat.Partrec.Code.eval .succ n = Part.none := by
  rw [math_no_numerical_iff, ← machineValue_none_iff, successorMachine_value]
  rfl

/-- Extend the finite-table base compiler with the successor code. -/
def compileSuccessorMachine (c : Nat.Partrec.Code) : Option (Σ states, Program states) :=
  if Encodable.encode c = Encodable.encode Nat.Partrec.Code.succ then some ⟨2, successorMachine⟩
  else compileBasicMachine c

theorem compileSuccessorMachine_succ :
    compileSuccessorMachine Nat.Partrec.Code.succ = some ⟨2, successorMachine⟩ := by
  simp [compileSuccessorMachine]

theorem compileSuccessorMachine_zero :
    compileSuccessorMachine Nat.Partrec.Code.zero = some ⟨1, zeroMachine⟩ := by
  have h : Encodable.encode Nat.Partrec.Code.zero ≠ Encodable.encode Nat.Partrec.Code.succ := by
    intro he
    have : Nat.Partrec.Code.zero = Nat.Partrec.Code.succ := Encodable.encode_injective he
    cases this
  simp [compileSuccessorMachine, h, compileBasicMachine_zero]

theorem compileSuccessorMachine_id :
    compileSuccessorMachine Nat.Partrec.Code.id = some ⟨0, immediateHalt⟩ := by
  have h : Encodable.encode Nat.Partrec.Code.id ≠ Encodable.encode Nat.Partrec.Code.succ := by
    intro he
    have : Nat.Partrec.Code.id = Nat.Partrec.Code.succ := Encodable.encode_injective he
    cases this
  simp [compileSuccessorMachine, h, compileBasicMachine_id]

theorem compileSuccessorMachine_sound (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileSuccessorMachine c = some p) (n : Nat) :
    machineValue p.2 n = Nat.Partrec.Code.eval c n := by
  by_cases hs : Encodable.encode c = Encodable.encode Nat.Partrec.Code.succ
  · have hp : (⟨2, successorMachine⟩ : Σ states, Program states) = p := by
      simpa [compileSuccessorMachine, hs] using h
    have hc : c = Nat.Partrec.Code.succ := Encodable.encode_injective hs
    subst p
    subst c
    exact successorMachine_value n
  · exact compileBasicMachine_sound c p (by simpa [compileSuccessorMachine, hs] using h) n

theorem compileSuccessorMachine_mathYields (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileSuccessorMachine c = some p) (n m : Nat) :
    MathYields p.2 n m ↔ m ∈ Nat.Partrec.Code.eval c n := by
  rw [math_yields_iff, ← mem_machineValue_iff, compileSuccessorMachine_sound c p h n]

theorem compileSuccessorMachine_mathNone (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileSuccessorMachine c = some p) (n : Nat) :
    (∀ m, ¬ MathYields p.2 n m) ↔ Nat.Partrec.Code.eval c n = Part.none := by
  rw [math_no_numerical_iff, ← machineValue_none_iff, compileSuccessorMachine_sound c p h n]

#print axioms successorMachine_mathYields
#print axioms successorMachine_mathNone
#print axioms compileSuccessorMachine_mathYields
#print axioms compileSuccessorMachine_mathNone

end LambdaTuring.Machine
