/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryShift
public meta import LambdaTuring.UnaryShift
public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable

@[expose] public section

namespace LambdaTuring.Machine

/-- Number a state of one five-state shift stage within the repeated machine. -/
def shiftPhaseState (k : Nat) (p : Fin k) (q : Fin 5) : Fin (5 * k + 1) :=
  ⟨p.val * 5 + q.val, by have := p.isLt; have := q.isLt; omega⟩

def shiftPhaseConfig (k : Nat) (p : Fin k) (c : Config 4) : Config (5 * k) :=
  ⟨shiftPhaseState k p c.state, c.tape⟩

def shiftRepeatInstruction (k : Nat) (q : Fin (5 * k + 1)) (s : Symbol) :
    Option (Fin (5 * k + 1) × Action) := by
  if hp : q.val / 5 < k then
    let phase : Fin k := ⟨q.val / 5, hp⟩
    let localState : Fin 5 := ⟨q.val % 5, Nat.mod_lt _ (by decide)⟩
    if localState.val = 4 ∧ s = .blank ∧ phase.val + 1 < k then
      exact some (shiftPhaseState k ⟨phase.val + 1, by omega⟩ ⟨0, by decide⟩, .right)
    else
      exact (instruction unaryShift localState s).map fun (q', a) =>
        (shiftPhaseState k phase q', a)
  else exact none

def shiftRepeat (k : Nat) : Program (5 * k) := tableOfFunction (shiftRepeatInstruction k)

theorem shiftPhaseState_div (k : Nat) (p : Fin k) (q : Fin 5) :
    (shiftPhaseState k p q).val / 5 = p.val := by
  simp only [shiftPhaseState]
  have := q.isLt
  omega

theorem shiftPhaseState_mod (k : Nat) (p : Fin k) (q : Fin 5) :
    (shiftPhaseState k p q).val % 5 = q.val := by
  simp [shiftPhaseState, Nat.add_mod, Nat.mod_eq_of_lt q.isLt]

theorem shiftRepeat_step (k : Nat) (p : Fin k) (a b : Config 4)
    (h : step unaryShift a = some b) :
    step (shiftRepeat k) (shiftPhaseConfig k p a) = some (shiftPhaseConfig k p b) := by
  have hn : ¬ (a.state.val = 4 ∧ a.tape.head = .blank) := by
    rintro ⟨hq, hs⟩
    have hq' : a.state = (⟨4, by decide⟩ : Fin 5) := Fin.ext hq
    cases a with
    | mk q t =>
      change q = (⟨4, by decide⟩ : Fin 5) at hq'
      subst q
      cases t with
      | mk l head r =>
        change head = .blank at hs
        subst head
        simp [step, instruction, unaryShift, symbolIndex] at h
  have hd : (shiftPhaseState k p a.state).val / 5 = p.val := shiftPhaseState_div k p a.state
  have hm : (shiftPhaseState k p a.state).val % 5 = a.state.val := shiftPhaseState_mod k p a.state
  have hp : (shiftPhaseState k p a.state).val / 5 < k := hd ▸ p.isLt
  have hphase : (⟨(shiftPhaseState k p a.state).val / 5, hp⟩ : Fin k) = p := Fin.ext hd
  have hlocal : (⟨(shiftPhaseState k p a.state).val % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = a.state := Fin.ext hm
  simp only [step, shiftRepeat, tableOfFunction_instruction, shiftPhaseConfig]
  unfold shiftRepeatInstruction
  rw [dite_eq_left hp]
  simp only [hphase, hlocal]
  have hcond : ¬ (a.state.val = 4 ∧ a.tape.head = .blank ∧ p.val + 1 < k) := by
    intro hcond
    exact hn ⟨hcond.1, hcond.2.1⟩
  simp only [hm, hd, hcond, ↓reduceDIte]
  cases hi : instruction unaryShift a.state a.tape.head with
  | none => simp [step, hi] at h
  | some pair =>
    rcases pair with ⟨q, act⟩
    have hb : b = ⟨q, perform act a.tape⟩ := by
      simpa [step, hi] using h.symm
    subst b
    rfl

theorem shiftRepeat_reaches (k : Nat) (p : Fin k) (a b : Config 4)
    (h : Reaches unaryShift a b) :
    Reaches (shiftRepeat k) (shiftPhaseConfig k p a) (shiftPhaseConfig k p b) := by
  induction h with
  | refl => exact .refl _
  | step hs hr ih => exact .step (shiftRepeat_step k p _ _ hs) ih

theorem shiftRepeat_continue (k : Nat) (p : Fin k) (h : p.val + 1 < k)
    (L : List Symbol) (n : Nat) :
    step (shiftRepeat k) (shiftPhaseConfig k p (shiftGap L n)) =
      some (shiftPhaseConfig k ⟨p.val + 1, h⟩ (shiftStart (.blank :: L) n)) := by
  have hp : (shiftPhaseState k p (⟨4, by decide⟩ : Fin 5)).val / 5 < k := by
    rw [shiftPhaseState_div]
    exact p.isLt
  simp only [step, shiftRepeat, tableOfFunction_instruction, shiftPhaseConfig, shiftGap]
  unfold shiftRepeatInstruction
  rw [dite_eq_left hp]
  simp [shiftPhaseState_div, shiftPhaseState_mod, h, shiftStart, perform, moveRight,
    List.replicate_succ]

theorem shiftRepeat_loop (k : Nat) (p : Fin k) (j : Nat) (h : p.val + j < k)
    (L : List Symbol) (n : Nat) :
    Reaches (shiftRepeat k) (shiftPhaseConfig k p (shiftStart L n))
      (shiftPhaseConfig k ⟨p.val + j, h⟩ (shiftGap (List.replicate j .blank ++ L) n)) := by
  induction j generalizing p L with
  | zero =>
    simpa using shiftRepeat_reaches k p _ _ (shiftStart_reaches L n)
  | succ j ih =>
    have hp : p.val + 1 < k := by omega
    let next : Fin k := ⟨p.val + 1, hp⟩
    have hnext : next.val + j < k := by simp only [next]; omega
    apply reaches_trans (b := shiftPhaseConfig k p (shiftGap L n))
    · exact shiftRepeat_reaches k p _ _ (shiftStart_reaches L n)
    · apply Reaches.step (shiftRepeat_continue k p hp L n)
      have tail := ih next hnext (.blank :: L)
      have hrep : List.replicate j Symbol.blank ++ .blank :: L =
          .blank :: (List.replicate j Symbol.blank ++ L) := by
        have hrep' := congrArg (fun xs : List Symbol => xs ++ L)
          (List.replicate_succ' (n := j) (a := Symbol.blank)).symm
        simpa [List.replicate_succ, List.append_assoc] using hrep'
      simpa [next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_succ, List.append_assoc, hrep] using tail

theorem shiftRepeat_final_halts (k : Nat) (p : Fin k) (h : p.val + 1 = k)
    (L : List Symbol) (n : Nat) :
    Halted (shiftRepeat k) (shiftPhaseConfig k p (shiftGap L n)) := by
  have hp : (shiftPhaseState k p (⟨4, by decide⟩ : Fin 5)).val / 5 < k := by
    rw [shiftPhaseState_div]
    exact p.isLt
  have hlast : ¬ p.val + 1 < k := by omega
  simp only [Halted, step, shiftRepeat, tableOfFunction_instruction, shiftPhaseConfig, shiftGap]
  unfold shiftRepeatInstruction
  rw [dite_eq_left hp]
  simp [shiftPhaseState_div, shiftPhaseState_mod, hlast, instruction, unaryShift, symbolIndex]

theorem shiftThirteen_reaches (L : List Symbol) (n : Nat) :
    Reaches (shiftRepeat 13) (shiftPhaseConfig 13 ⟨0, by decide⟩ (shiftStart L n))
      (shiftPhaseConfig 13 ⟨12, by decide⟩ (shiftGap (List.replicate 12 .blank ++ L) n)) := by
  simpa using shiftRepeat_loop 13 ⟨0, by decide⟩ 12 (by decide) L n

theorem shiftThirteen_halts (L : List Symbol) (n : Nat) :
    Halted (shiftRepeat 13)
      (shiftPhaseConfig 13 ⟨12, by decide⟩ (shiftGap (List.replicate 12 .blank ++ L) n)) := by
  exact shiftRepeat_final_halts 13 ⟨12, by decide⟩ (by decide) _ _

#eval (shiftRepeat 13).table.length
#print axioms shiftRepeat_step
#print axioms shiftRepeat_reaches
#print axioms shiftRepeat_loop
#print axioms shiftThirteen_reaches
#print axioms shiftThirteen_halts
end LambdaTuring.Machine
