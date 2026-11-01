/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineSearch
public meta import LambdaTuring.MachineSearch
public import LambdaTuring.MathlibBridge
public meta import LambdaTuring.MathlibBridge
public import Mathlib.Computability.PartrecCode

@[expose] public section

namespace LambdaTuring.Machine

theorem immediateHalt_yields (n : Nat) : Yields immediateHalt n n := by
  refine ⟨initial n, .refl _, ?_, ?_⟩
  · rfl
  · simpa [initial, input, List.replicate_succ] using decode_input n

theorem immediateHalt_yields_iff (n m : Nat) : Yields immediateHalt n m ↔ m = n := by
  constructor
  · intro h
    exact yields_unique h (immediateHalt_yields n)
  · intro h
    subst m
    exact immediateHalt_yields n

theorem immediateHalt_value (n : Nat) : machineValue immediateHalt n = Part.some n := by
  apply Part.ext
  intro m
  rw [mem_machineValue_iff, immediateHalt_yields_iff]
  simp

/-- Construct a finite-table machine for Mathlib's identity code. Other codes
    are unsupported by this fragment; `none` does not denote divergence. -/
def compileIdentityMachine (c : Nat.Partrec.Code) : Option (Program 0) :=
  if Encodable.encode c = Encodable.encode Nat.Partrec.Code.id then some immediateHalt else none

theorem compileIdentityMachine_id : compileIdentityMachine Nat.Partrec.Code.id = some immediateHalt := by
  simp [compileIdentityMachine]

theorem compileIdentityMachine_sound (c : Nat.Partrec.Code) (p : Program 0)
    (h : compileIdentityMachine c = some p) (n : Nat) :
    machineValue p n = Nat.Partrec.Code.eval c n := by
  by_cases he : Encodable.encode c = Encodable.encode Nat.Partrec.Code.id
  · have hp : immediateHalt = p := by simpa [compileIdentityMachine, he] using h
    have hc : c = Nat.Partrec.Code.id := Encodable.encode_injective he
    subst p
    subst c
    rw [Nat.Partrec.Code.eval_id]
    exact immediateHalt_value n
  · simp [compileIdentityMachine, he] at h

theorem compileIdentityMachine_mathYields (c : Nat.Partrec.Code) (p : Program 0)
    (h : compileIdentityMachine c = some p) (n m : Nat) :
    MathYields p n m ↔ m ∈ Nat.Partrec.Code.eval c n := by
  rw [math_yields_iff, ← mem_machineValue_iff, compileIdentityMachine_sound c p h n]

theorem compileIdentityMachine_mathNone (c : Nat.Partrec.Code) (p : Program 0)
    (h : compileIdentityMachine c = some p) (n : Nat) :
    (∀ m, ¬ MathYields p n m) ↔ Nat.Partrec.Code.eval c n = Part.none := by
  rw [math_no_numerical_iff, ← machineValue_none_iff, compileIdentityMachine_sound c p h n]

/-- Scan to the first blank, write one, and halt. The cells to the left are
    intentionally ignored by the output decoder. -/
def zeroMachine : Program 1 :=
  ⟨[some (⟨1, by decide⟩, .write .one), some (⟨0, by decide⟩, .right)]⟩

def zeroScan (written remaining : Nat) : Config 1 :=
  ⟨⟨0, by decide⟩, ⟨List.replicate written .one, .one, List.replicate remaining .one⟩⟩

def zeroBlank (written : Nat) : Config 1 :=
  ⟨⟨0, by decide⟩, ⟨List.replicate written .one, .blank, []⟩⟩

def zeroHalt (written : Nat) : Config 1 :=
  ⟨⟨1, by decide⟩, ⟨List.replicate written .one, .one, []⟩⟩

theorem zeroScan_next (written remaining : Nat) :
    step zeroMachine (zeroScan written (remaining + 1)) = some (zeroScan (written + 1) remaining) := by
  simp [zeroMachine, zeroScan, step, instruction, symbolIndex, perform, moveRight, List.replicate_succ]

theorem zeroScan_last (written : Nat) :
    step zeroMachine (zeroScan written 0) = some (zeroBlank (written + 1)) := by
  simp [zeroMachine, zeroScan, zeroBlank, step, instruction, symbolIndex, perform, moveRight, List.replicate_succ]

theorem zeroScan_reaches (written remaining : Nat) :
    Reaches zeroMachine (zeroScan written remaining) (zeroBlank (written + remaining + 1)) := by
  induction remaining generalizing written with
  | zero => simpa using Reaches.step (zeroScan_last written) (Reaches.refl _)
  | succ remaining ih =>
    have h := Reaches.step (zeroScan_next written remaining) (ih (written + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem zeroBlank_next (written : Nat) :
    step zeroMachine (zeroBlank written) = some (zeroHalt written) := by
  rfl

theorem zeroHalt_halted (written : Nat) : Halted zeroMachine (zeroHalt written) := by
  rfl

theorem reaches_trans {states : Nat} {p : Program states} {a b c : Config states}
    (hab : Reaches p a b) (hbc : Reaches p b c) : Reaches p a c := by
  induction hab with
  | refl => exact hbc
  | step hs _ ih => exact .step hs (ih hbc)

theorem zeroMachine_yields (n : Nat) : Yields zeroMachine n 0 := by
  refine ⟨zeroHalt (n + 1), ?_, zeroHalt_halted _, ?_⟩
  · apply reaches_trans (b := zeroBlank (n + 1))
    · simpa [zeroScan, initial] using zeroScan_reaches 0 n
    · exact .step (zeroBlank_next _) (.refl _)
  · rfl

theorem zeroMachine_yields_iff (n m : Nat) : Yields zeroMachine n m ↔ m = 0 := by
  constructor
  · intro h
    exact yields_unique h (zeroMachine_yields n)
  · intro h
    subst m
    exact zeroMachine_yields n

theorem zeroMachine_value (n : Nat) : machineValue zeroMachine n = Part.some 0 := by
  apply Part.ext
  intro m
  rw [mem_machineValue_iff, zeroMachine_yields_iff]
  simp

/-- The base machine compiler returns finite transition tables for the zero
    and identity codes. Unsupported codes are reported explicitly. -/
def compileBasicMachine (c : Nat.Partrec.Code) : Option (Σ states, Program states) :=
  if Encodable.encode c = Encodable.encode Nat.Partrec.Code.id then some ⟨0, immediateHalt⟩
  else if Encodable.encode c = Encodable.encode Nat.Partrec.Code.zero then some ⟨1, zeroMachine⟩
  else none

theorem compileBasicMachine_id : compileBasicMachine Nat.Partrec.Code.id = some ⟨0, immediateHalt⟩ := by
  simp [compileBasicMachine]

theorem compileBasicMachine_zero : compileBasicMachine Nat.Partrec.Code.zero = some ⟨1, zeroMachine⟩ := by
  have h : Encodable.encode Nat.Partrec.Code.zero ≠ Encodable.encode Nat.Partrec.Code.id := by
    intro he
    have : Nat.Partrec.Code.zero = Nat.Partrec.Code.id := Encodable.encode_injective he
    cases this
  simp [compileBasicMachine, h]

theorem compileBasicMachine_sound (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileBasicMachine c = some p) (n : Nat) :
    machineValue p.2 n = Nat.Partrec.Code.eval c n := by
  by_cases hi : Encodable.encode c = Encodable.encode Nat.Partrec.Code.id
  · have hp : (⟨0, immediateHalt⟩ : Σ states, Program states) = p := by
      simpa [compileBasicMachine, hi] using h
    have hc : c = Nat.Partrec.Code.id := Encodable.encode_injective hi
    subst p
    subst c
    rw [Nat.Partrec.Code.eval_id]
    exact immediateHalt_value n
  · by_cases hz : Encodable.encode c = Encodable.encode Nat.Partrec.Code.zero
    · have hp : (⟨1, zeroMachine⟩ : Σ states, Program states) = p := by
        simp only [compileBasicMachine, ite_eq_right hi, ite_eq_left hz, Option.some.injEq] at h
        exact h
      have hc : c = Nat.Partrec.Code.zero := Encodable.encode_injective hz
      subst p
      subst c
      exact zeroMachine_value n
    · simp [compileBasicMachine, hi, hz] at h

theorem compileBasicMachine_mathYields (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileBasicMachine c = some p) (n m : Nat) :
    MathYields p.2 n m ↔ m ∈ Nat.Partrec.Code.eval c n := by
  rw [math_yields_iff, ← mem_machineValue_iff, compileBasicMachine_sound c p h n]

theorem compileBasicMachine_mathNone (c : Nat.Partrec.Code) (p : Σ states, Program states)
    (h : compileBasicMachine c = some p) (n : Nat) :
    (∀ m, ¬ MathYields p.2 n m) ↔ Nat.Partrec.Code.eval c n = Part.none := by
  rw [math_no_numerical_iff, ← machineValue_none_iff, compileBasicMachine_sound c p h n]

#print axioms compileIdentityMachine_mathYields
#print axioms compileIdentityMachine_mathNone
#print axioms compileBasicMachine_mathYields
#print axioms compileBasicMachine_mathNone

end LambdaTuring.Machine
