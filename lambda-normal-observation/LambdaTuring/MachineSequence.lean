/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable
public import LambdaTuring.MachineCompilerBase
public meta import LambdaTuring.MachineCompilerBase

@[expose] public section

namespace LambdaTuring.Machine

def sequenceLeftState (n m : Nat) (q : Fin (n + 1)) : Fin (n + m + 2) :=
  ⟨q.val, by have := q.isLt; omega⟩

def sequenceRightState (n m : Nat) (q : Fin (m + 1)) : Fin (n + m + 2) :=
  ⟨n + 1 + q.val, by have := q.isLt; omega⟩

def sequenceLeftConfig {n m : Nat} (c : Config n) : Config (n + m + 1) :=
  ⟨sequenceLeftState n m c.state, c.tape⟩

def sequenceRightConfig {n m : Nat} (c : Config m) : Config (n + m + 1) :=
  ⟨sequenceRightState n m c.state, c.tape⟩

/-- Run the first table until it halts, then enter the second table without
changing the tape. The caller must establish the desired intermediate invariant. -/
def sequenceInstruction {n m : Nat} (a : Program n) (b : Program m)
    (q : Fin (n + m + 2)) (s : Symbol) : Option (Fin (n + m + 2) × Action) := by
  if h : q.val < n + 1 then
    match instruction a ⟨q.val, h⟩ s with
    | some (r, act) => exact some (sequenceLeftState n m r, act)
    | none => exact some (sequenceRightState n m ⟨0, Nat.zero_lt_succ m⟩, .write s)
  else
    let r : Fin (m + 1) := ⟨q.val - (n + 1), by have := q.isLt; omega⟩
    exact (instruction b r s).map fun (r', act) => (sequenceRightState n m r', act)

def sequenceProgram {n m : Nat} (a : Program n) (b : Program m) : Program (n + m + 1) :=
  tableOfFunction (sequenceInstruction a b)

theorem sequence_left_step {n m : Nat} (a : Program n) (b : Program m) (c d : Config n)
    (h : step a c = some d) :
    step (sequenceProgram a b) (sequenceLeftConfig c) = some (sequenceLeftConfig d) := by
  have hc : (sequenceLeftState n m c.state).val < n + 1 := c.state.isLt
  simp only [step, sequenceProgram, tableOfFunction_instruction, sequenceLeftConfig]
  unfold sequenceInstruction
  rw [dite_eq_left hc]
  have he : (⟨(sequenceLeftState n m c.state).val, hc⟩ : Fin (n + 1)) = c.state := rfl
  rw [he]
  cases hi : instruction a c.state c.tape.head with
  | none => simp [step, hi] at h
  | some v =>
    rcases v with ⟨q, act⟩
    have hd : d = ⟨q, perform act c.tape⟩ := by simpa [step, hi] using h.symm
    subst d
    rfl

theorem sequence_left_reaches {n m : Nat} (a : Program n) (b : Program m) (c d : Config n)
    (h : Reaches a c d) :
    Reaches (sequenceProgram a b) (sequenceLeftConfig c) (sequenceLeftConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih => exact .step (sequence_left_step a b _ _ hs) ih

theorem sequence_switch {n m : Nat} (a : Program n) (b : Program m) (c : Config n)
    (h : Halted a c) :
    step (sequenceProgram a b) (sequenceLeftConfig c) =
      some (sequenceRightConfig (⟨⟨0, Nat.zero_lt_succ m⟩, c.tape⟩ : Config m)) := by
  have hc : (sequenceLeftState n m c.state).val < n + 1 := c.state.isLt
  have hi : instruction a c.state c.tape.head = none := by
    cases h' : instruction a c.state c.tape.head with
    | none => rfl
    | some v => simp [Halted, step, h'] at h
  simp only [step, sequenceProgram, tableOfFunction_instruction, sequenceLeftConfig]
  unfold sequenceInstruction
  rw [dite_eq_left hc]
  have he : (⟨(sequenceLeftState n m c.state).val, hc⟩ : Fin (n + 1)) = c.state := rfl
  rw [he, hi]
  cases c.tape
  rfl

theorem sequence_right_step {n m : Nat} (a : Program n) (b : Program m) (c : Config m) :
    step (sequenceProgram a b) (sequenceRightConfig c) =
      (step b c).map sequenceRightConfig := by
  have hc : ¬ (sequenceRightState n m c.state).val < n + 1 := by
    simp [sequenceRightState]
  have he : (⟨(sequenceRightState n m c.state).val - (n + 1), by
      have := (sequenceRightState n m c.state).isLt; omega⟩ : Fin (m + 1)) = c.state := by
    apply Fin.ext
    simp [sequenceRightState]
  simp only [step, sequenceProgram, tableOfFunction_instruction, sequenceRightConfig]
  unfold sequenceInstruction
  rw [dite_eq_right hc]
  simp only [he]
  cases hi : instruction b c.state c.tape.head with
  | none => rfl
  | some v => rcases v with ⟨q, act⟩; rfl

theorem sequence_right_reaches {n m : Nat} (a : Program n) (b : Program m) (c d : Config m)
    (h : Reaches b c d) :
    Reaches (sequenceProgram a b) (sequenceRightConfig c) (sequenceRightConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih =>
    apply Reaches.step ?_ ih
    rw [sequence_right_step, hs]
    rfl

theorem sequence_right_halts {n m : Nat} (a : Program n) (b : Program m) (c : Config m)
    (h : Halted b c) : Halted (sequenceProgram a b) (sequenceRightConfig c) := by
  change step (sequenceProgram a b) (sequenceRightConfig c) = none
  rw [sequence_right_step, h]
  rfl

theorem sequence_complete {n m : Nat} (a : Program n) (b : Program m)
    (start mid : Config n) (finish : Config m)
    (hfirst : Reaches a start mid) (hfirstHalt : Halted a mid)
    (hsecond : Reaches b ⟨⟨0, Nat.zero_lt_succ m⟩, mid.tape⟩ finish)
    (hsecondHalt : Halted b finish) :
    Reaches (sequenceProgram a b) (sequenceLeftConfig start) (sequenceRightConfig finish) ∧
      Halted (sequenceProgram a b) (sequenceRightConfig finish) := by
  constructor
  · apply reaches_trans (sequence_left_reaches a b start mid hfirst)
    exact .step (sequence_switch a b mid hfirstHalt) (sequence_right_reaches a b _ _ hsecond)
  · exact sequence_right_halts a b finish hsecondHalt

#print axioms sequence_complete
end LambdaTuring.Machine
