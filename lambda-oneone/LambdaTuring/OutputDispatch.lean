/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.OutputSafeBridge
public meta import LambdaTuring.OutputSafeBridge

@[expose] public section

namespace LambdaTuring.Machine

def readLoopReaderState (n m k : Nat) (q : Fin (n+1)) : Fin (n+m+k+3) :=
  ⟨q.val, by have := q.isLt; omega⟩

def readLoopBodyState (n m k : Nat) (q : Fin (m+1)) : Fin (n+m+k+3) :=
  ⟨n+1+q.val, by have := q.isLt; omega⟩

def readLoopFinalState (n m k : Nat) (q : Fin (k+1)) : Fin (n+m+k+3) :=
  ⟨n+1+(m+1)+q.val, by have := q.isLt; omega⟩

def readLoopReaderConfig {n m k : Nat} (c : Config n) : Config (n+m+k+2) :=
  ⟨readLoopReaderState n m k c.state, c.tape⟩

def readLoopBodyConfig {n m k : Nat} (c : Config m) : Config (n+m+k+2) :=
  ⟨readLoopBodyState n m k c.state, c.tape⟩

def readLoopFinalConfig {n m k : Nat} (c : Config k) : Config (n+m+k+2) :=
  ⟨readLoopFinalState n m k c.state, c.tape⟩

/- A terminal reader state chooses body, final, or a malformed halt. A body
halt returns to the reader; final-stage instructions retain their semantics. -/
def readLoopInstruction {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (q : Fin (n+m+k+3)) (s : Symbol) :
    Option (Fin (n+m+k+3) × Action) := by
  if hr : q.val < n+1 then
    let i : Fin (n+1) := ⟨q.val, hr⟩
    match instruction reader i s with
    | some (j, act) => exact some (readLoopReaderState n m k j, act)
    | none =>
      match classify i with
      | some true => exact some (readLoopBodyState n m k ⟨0, by omega⟩, .write s)
      | some false => exact some (readLoopFinalState n m k ⟨0, by omega⟩, .write s)
      | none => exact none
  else if hb : q.val < n+1+(m+1) then
    let i : Fin (m+1) := ⟨q.val-(n+1), by omega⟩
    match instruction body i s with
    | some (j, act) => exact some (readLoopBodyState n m k j, act)
    | none => exact some (readLoopReaderState n m k ⟨0, by omega⟩, .write s)
  else
    let i : Fin (k+1) := ⟨q.val-(n+1+(m+1)), by have := q.isLt; omega⟩
    exact (instruction last i s).map fun (j, act) => (readLoopFinalState n m k j, act)

def readLoopProgram {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) : Program (n+m+k+2) :=
  tableOfFunction (readLoopInstruction reader body last classify)

theorem readLoop_reader_step {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c d : Config n) (h : step reader c = some d) :
    step (readLoopProgram reader body last classify) (readLoopReaderConfig (m := m) (k := k) c) =
      some (readLoopReaderConfig d) := by
  have hr : (readLoopReaderState n m k c.state).val < n+1 := by
    simp [readLoopReaderState, c.state.isLt]
  have hi : (⟨(readLoopReaderState n m k c.state).val, hr⟩ : Fin (n+1)) = c.state := by
    apply Fin.ext; rfl
  simp only [step, readLoopProgram, tableOfFunction_instruction, readLoopReaderConfig]
  unfold readLoopInstruction
  rw [dite_eq_left hr]
  simp only [hi]
  cases he : instruction reader c.state c.tape.head with
  | none => simp [step, he] at h
  | some v =>
    rcases v with ⟨q, act⟩
    have hd : d = ⟨q, perform act c.tape⟩ := by simpa [step, he] using h.symm
    subst d
    rfl

theorem readLoop_reader_reaches {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c d : Config n) (h : Reaches reader c d) :
    Reaches (readLoopProgram reader body last classify)
      (readLoopReaderConfig (m := m) (k := k) c) (readLoopReaderConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (readLoop_reader_step reader body last classify _ _ hs) ih

theorem readLoop_reader_halt {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c : Config n) (h : Halted reader c) (b : Bool)
    (hc : classify c.state = some b) :
    step (readLoopProgram reader body last classify) (readLoopReaderConfig (m := m) (k := k) c) =
      some (if b then readLoopBodyConfig ⟨⟨0, by omega⟩, c.tape⟩
        else readLoopFinalConfig ⟨⟨0, by omega⟩, c.tape⟩) := by
  have hr : (readLoopReaderState n m k c.state).val < n+1 := by
    simp [readLoopReaderState, c.state.isLt]
  have hi : (⟨(readLoopReaderState n m k c.state).val, hr⟩ : Fin (n+1)) = c.state := by
    apply Fin.ext; rfl
  have hs : instruction reader c.state c.tape.head = none := by
    cases he : instruction reader c.state c.tape.head with
    | none => rfl
    | some x => simp [Halted, step, he] at h
  simp only [step, readLoopProgram, tableOfFunction_instruction, readLoopReaderConfig]
  unfold readLoopInstruction
  rw [dite_eq_left hr]
  simp only [hi, hs, hc]
  cases b <;> cases c.tape <;> rfl

theorem readLoop_body_step {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c d : Config m) (h : step body c = some d) :
    step (readLoopProgram reader body last classify) (readLoopBodyConfig (n := n) (k := k) c) =
      some (readLoopBodyConfig d) := by
  have hr : ¬ (readLoopBodyState n m k c.state).val < n+1 := by simp [readLoopBodyState]
  have hb : (readLoopBodyState n m k c.state).val < n+1+(m+1) := by
    simp only [readLoopBodyState]; have := c.state.isLt; omega
  have hi : (⟨(readLoopBodyState n m k c.state).val-(n+1), by simp [readLoopBodyState]⟩ : Fin (m+1)) =
      c.state := by apply Fin.ext; simp [readLoopBodyState]
  simp only [step, readLoopProgram, tableOfFunction_instruction, readLoopBodyConfig]
  unfold readLoopInstruction
  rw [dite_eq_right hr, dite_eq_left hb]
  simp only [hi]
  cases he : instruction body c.state c.tape.head with
  | none => simp [step, he] at h
  | some v =>
    rcases v with ⟨q, act⟩
    have hd : d = ⟨q, perform act c.tape⟩ := by simpa [step, he] using h.symm
    subst d
    rfl

theorem readLoop_body_reaches {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c d : Config m) (h : Reaches body c d) :
    Reaches (readLoopProgram reader body last classify)
      (readLoopBodyConfig (n := n) (k := k) c) (readLoopBodyConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step (readLoop_body_step reader body last classify _ _ hs) ih

theorem readLoop_body_halt {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c : Config m) (h : Halted body c) :
    step (readLoopProgram reader body last classify) (readLoopBodyConfig (n := n) (k := k) c) =
      some (readLoopReaderConfig ⟨⟨0, by omega⟩, c.tape⟩) := by
  have hr : ¬ (readLoopBodyState n m k c.state).val < n+1 := by simp [readLoopBodyState]
  have hb : (readLoopBodyState n m k c.state).val < n+1+(m+1) := by
    simp only [readLoopBodyState]; have := c.state.isLt; omega
  have hi : (⟨(readLoopBodyState n m k c.state).val-(n+1), by simp [readLoopBodyState]⟩ : Fin (m+1)) =
      c.state := by apply Fin.ext; simp [readLoopBodyState]
  have hs : instruction body c.state c.tape.head = none := by
    cases he : instruction body c.state c.tape.head with
    | none => rfl
    | some x => simp [Halted, step, he] at h
  simp only [step, readLoopProgram, tableOfFunction_instruction, readLoopBodyConfig]
  unfold readLoopInstruction
  rw [dite_eq_right hr, dite_eq_left hb]
  simp only [hi, hs]
  cases c.tape
  rfl

theorem readLoop_final_step {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c : Config k) :
    step (readLoopProgram reader body last classify) (readLoopFinalConfig (n := n) (m := m) c) =
      (step last c).map readLoopFinalConfig := by
  have hr : ¬ (readLoopFinalState n m k c.state).val < n+1 := by
    simp only [readLoopFinalState]; omega
  have hb : ¬ (readLoopFinalState n m k c.state).val < n+1+(m+1) := by simp [readLoopFinalState]
  have hi : (⟨(readLoopFinalState n m k c.state).val-(n+1+(m+1)), by
      have := (readLoopFinalState n m k c.state).isLt; omega⟩ : Fin (k+1)) = c.state := by
    apply Fin.ext; simp [readLoopFinalState]
  simp only [step, readLoopProgram, tableOfFunction_instruction, readLoopFinalConfig]
  unfold readLoopInstruction
  rw [dite_eq_right hr, dite_eq_right hb]
  simp only [hi]
  cases he : instruction last c.state c.tape.head with
  | none => rfl
  | some x => rcases x with ⟨q, act⟩; rfl

theorem readLoop_final_reaches {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c d : Config k) (h : Reaches last c d) :
    Reaches (readLoopProgram reader body last classify)
      (readLoopFinalConfig (n := n) (m := m) c) (readLoopFinalConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    apply Reaches.step ?_ ih
    rw [readLoop_final_step, hs]
    rfl

theorem readLoop_final_halt {n m k : Nat} (reader : Program n) (body : Program m) (last : Program k)
    (classify : Fin (n+1) → Option Bool) (c : Config k) (h : Halted last c) :
    Halted (readLoopProgram reader body last classify) (readLoopFinalConfig (n := n) (m := m) c) := by
  change step (readLoopProgram reader body last classify) (readLoopFinalConfig c) = none
  rw [readLoop_final_step, h]
  rfl

#print axioms readLoop_reader_reaches
#print axioms readLoop_reader_halt
#print axioms readLoop_body_reaches
#print axioms readLoop_final_reaches
end LambdaTuring.Machine
