/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ConsumeAndInsert
public meta import LambdaTuring.ConsumeAndInsert

@[expose] public section

namespace LambdaTuring.Machine

def loopControlState (n m : Nat) (i : Fin 4) : Fin (n + m + 6) :=
  ⟨i.val, by have := i.isLt; omega⟩

def loopBodyState (n m : Nat) (i : Fin (n + 1)) : Fin (n + m + 6) :=
  ⟨4 + i.val, by have := i.isLt; omega⟩

def loopFinalState (n m : Nat) (i : Fin (m + 1)) : Fin (n + m + 6) :=
  ⟨4 + (n + 1) + i.val, by have := i.isLt; omega⟩

def loopBodyConfig {n m : Nat} (c : Config n) : Config (n + m + 5) :=
  ⟨loopBodyState n m c.state, c.tape⟩

def loopFinalConfig {n m : Nat} (c : Config m) : Config (n + m + 5) :=
  ⟨loopFinalState n m c.state, c.tape⟩

def loopCheckConfig (n m : Nat) (i : Fin 4) (t : Tape) : Config (n + m + 5) :=
  ⟨loopControlState n m i, t⟩

/-- Inspect the next cell to choose the body or final stage. A body halt
returns to the check; a final-stage halt remains terminal. -/
def loopInstruction {n m : Nat} (body : Program n) (last : Program m)
    (q : Fin (n + m + 6)) (s : Symbol) : Option (Fin (n + m + 6) × Action) := by
  if hcontrol : q.val < 4 then
    match q.val with
    | 0 => if s = .one then exact some (loopControlState n m ⟨1, by decide⟩, .right) else exact none
    | 1 =>
      match s with
      | .one => exact some (loopControlState n m ⟨2, by decide⟩, .left)
      | .blank => exact some (loopControlState n m ⟨3, by decide⟩, .left)
      | .mark => exact none
    | 2 => exact some (loopBodyState n m ⟨0, Nat.zero_lt_succ n⟩, .write s)
    | _ => exact some (loopFinalState n m ⟨0, Nat.zero_lt_succ m⟩, .write s)
  else if hbody : q.val < 4 + (n + 1) then
    let i : Fin (n + 1) := ⟨q.val - 4, by omega⟩
    match instruction body i s with
    | some (r, act) => exact some (loopBodyState n m r, act)
    | none => exact some (loopControlState n m ⟨0, by decide⟩, .write s)
  else
    let i : Fin (m + 1) := ⟨q.val - (4 + (n + 1)), by have := q.isLt; omega⟩
    exact (instruction last i s).map fun (r, act) => (loopFinalState n m r, act)

def loopProgram {n m : Nat} (body : Program n) (last : Program m) : Program (n + m + 5) :=
  tableOfFunction (loopInstruction body last)

theorem loop_body_step {n m : Nat} (body : Program n) (last : Program m) (c d : Config n)
    (h : step body c = some d) :
    step (loopProgram body last) (loopBodyConfig c) = some (loopBodyConfig d) := by
  have hc : ¬ (loopBodyState n m c.state).val < 4 := by simp [loopBodyState]
  have hb : (loopBodyState n m c.state).val < 4 + (n + 1) := by
    simp only [loopBodyState]; have := c.state.isLt; omega
  have hi : (⟨(loopBodyState n m c.state).val - 4, by simp [loopBodyState]⟩ : Fin (n + 1)) = c.state := by
    apply Fin.ext; simp [loopBodyState]
  simp only [step, loopProgram, tableOfFunction_instruction, loopBodyConfig]
  unfold loopInstruction
  rw [dite_eq_right hc, dite_eq_left hb]
  simp only [hi]
  cases hs : instruction body c.state c.tape.head with
  | none => simp [step, hs] at h
  | some v =>
    rcases v with ⟨q, act⟩
    have hd : d = ⟨q, perform act c.tape⟩ := by simpa [step, hs] using h.symm
    subst d
    rfl

theorem loop_body_reaches {n m : Nat} (body : Program n) (last : Program m) (c d : Config n)
    (h : Reaches body c d) :
    Reaches (loopProgram body last) (loopBodyConfig c) (loopBodyConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih => exact .step (loop_body_step body last _ _ hs) ih

theorem loop_body_halt {n m : Nat} (body : Program n) (last : Program m) (c : Config n)
    (h : Halted body c) :
    step (loopProgram body last) (loopBodyConfig c) = some (loopCheckConfig n m ⟨0, by decide⟩ c.tape) := by
  have hc : ¬ (loopBodyState n m c.state).val < 4 := by simp [loopBodyState]
  have hb : (loopBodyState n m c.state).val < 4 + (n + 1) := by
    simp only [loopBodyState]; have := c.state.isLt; omega
  have hi : (⟨(loopBodyState n m c.state).val - 4, by simp [loopBodyState]⟩ : Fin (n + 1)) = c.state := by
    apply Fin.ext; simp [loopBodyState]
  have hs : instruction body c.state c.tape.head = none := by
    cases he : instruction body c.state c.tape.head with
    | none => rfl
    | some x => simp [Halted, step, he] at h
  simp only [step, loopProgram, tableOfFunction_instruction, loopBodyConfig]
  unfold loopInstruction
  rw [dite_eq_right hc, dite_eq_left hb]
  simp only [hi, hs]
  cases c.tape
  rfl

theorem loop_final_step {n m : Nat} (body : Program n) (last : Program m) (c : Config m) :
    step (loopProgram body last) (loopFinalConfig c) = (step last c).map loopFinalConfig := by
  have hc : ¬ (loopFinalState n m c.state).val < 4 := by simp only [loopFinalState]; omega
  have hb : ¬ (loopFinalState n m c.state).val < 4 + (n + 1) := by simp [loopFinalState]
  have hi : (⟨(loopFinalState n m c.state).val - (4 + (n + 1)), by
      have := (loopFinalState n m c.state).isLt; omega⟩ : Fin (m + 1)) = c.state := by
    apply Fin.ext; simp [loopFinalState]
  simp only [step, loopProgram, tableOfFunction_instruction, loopFinalConfig]
  unfold loopInstruction
  rw [dite_eq_right hc, dite_eq_right hb]
  simp only [hi]
  cases he : instruction last c.state c.tape.head with
  | none => rfl
  | some x => rcases x with ⟨q, act⟩; rfl

theorem loop_final_reaches {n m : Nat} (body : Program n) (last : Program m) (c d : Config m)
    (h : Reaches last c d) :
    Reaches (loopProgram body last) (loopFinalConfig c) (loopFinalConfig d) := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih =>
    apply Reaches.step ?_ ih
    rw [loop_final_step, hs]
    rfl

theorem loop_final_halt {n m : Nat} (body : Program n) (last : Program m) (c : Config m)
    (h : Halted last c) : Halted (loopProgram body last) (loopFinalConfig c) := by
  change step (loopProgram body last) (loopFinalConfig c) = none
  rw [loop_final_step, h]
  rfl

theorem loop_check_more {n m : Nat} (body : Program n) (last : Program m)
    (L : List Symbol) (k : Nat) :
    Reaches (loopProgram body last)
      (loopCheckConfig n m ⟨0, by decide⟩ ⟨L, .one, .one :: List.replicate k .one⟩)
      (loopBodyConfig (⟨⟨0, Nat.zero_lt_succ n⟩, ⟨L, .one, .one :: List.replicate k .one⟩⟩ : Config n)) := by
  apply Reaches.step (b := loopCheckConfig n m ⟨1, by decide⟩
    ⟨.one :: L, .one, List.replicate k .one⟩)
  · simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
      loopInstruction, perform, moveRight]
  · apply Reaches.step (b := loopCheckConfig n m ⟨2, by decide⟩
      ⟨L, .one, .one :: List.replicate k .one⟩)
    · simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
        loopInstruction, perform, moveLeft]
    · apply Reaches.step ?_ (.refl _)
      simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
        loopBodyConfig, loopInstruction, perform]

theorem loop_check_last {n m : Nat} (body : Program n) (last : Program m) (L : List Symbol) :
    Reaches (loopProgram body last)
      (loopCheckConfig n m ⟨0, by decide⟩ ⟨L, .one, []⟩)
      (loopFinalConfig (⟨⟨0, Nat.zero_lt_succ m⟩, ⟨L, .one, [.blank]⟩⟩ : Config m)) := by
  apply Reaches.step (b := loopCheckConfig n m ⟨1, by decide⟩ ⟨.one :: L, .blank, []⟩)
  · simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
      loopInstruction, perform, moveRight]
  · apply Reaches.step (b := loopCheckConfig n m ⟨3, by decide⟩ ⟨L, .one, [.blank]⟩)
    · simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
        loopInstruction, perform, moveLeft]
    · apply Reaches.step ?_ (.refl _)
      simp [step, loopProgram, tableOfFunction_instruction, loopCheckConfig, loopControlState,
        loopFinalConfig, loopInstruction, perform]

#print axioms loop_body_reaches
#print axioms loop_final_reaches
#print axioms loop_check_more
#print axioms loop_check_last
end LambdaTuring.Machine
