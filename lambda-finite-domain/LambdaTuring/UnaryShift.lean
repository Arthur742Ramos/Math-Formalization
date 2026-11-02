/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineSuccessor
public meta import LambdaTuring.MachineSuccessor

@[expose] public section

namespace LambdaTuring.Machine

/-- Move a nonempty unary run one cell to the right, leaving a blank at its
original head. Entries for markers halt; the theorem assumes a unary run. -/
def unaryShift : Program 4 :=
  ⟨[none, some (⟨1, by decide⟩, .write .blank), none,
    some (⟨2, by decide⟩, .right), none, none,
    some (⟨3, by decide⟩, .write .one), some (⟨2, by decide⟩, .right), none,
    none, some (⟨4, by decide⟩, .left), none,
    none, some (⟨4, by decide⟩, .left), none]⟩

def shiftStart (L : List Symbol) (n : Nat) : Config 4 :=
  ⟨⟨0, by decide⟩, ⟨L, .one, List.replicate n .one⟩⟩
def shiftErase (L : List Symbol) (n : Nat) : Config 4 :=
  ⟨⟨1, by decide⟩, ⟨L, .blank, List.replicate n .one⟩⟩
def shiftScan (L : List Symbol) (seen remaining : Nat) : Config 4 :=
  ⟨⟨2, by decide⟩, ⟨List.replicate seen .one ++ .blank :: L, .one, List.replicate remaining .one⟩⟩
def shiftEnd (L : List Symbol) (seen : Nat) : Config 4 :=
  ⟨⟨2, by decide⟩, ⟨List.replicate seen .one ++ .blank :: L, .blank, []⟩⟩
def shiftWritten (L : List Symbol) (seen : Nat) : Config 4 :=
  ⟨⟨3, by decide⟩, ⟨List.replicate seen .one ++ .blank :: L, .one, []⟩⟩
def shiftReturn (L : List Symbol) (left right : Nat) : Config 4 :=
  ⟨⟨4, by decide⟩, ⟨List.replicate left .one ++ .blank :: L, .one, List.replicate right .one⟩⟩
def shiftGap (L : List Symbol) (n : Nat) : Config 4 :=
  ⟨⟨4, by decide⟩, ⟨L, .blank, List.replicate (n + 1) .one⟩⟩

theorem shiftStart_next (L : List Symbol) (n : Nat) :
    step unaryShift (shiftStart L n) = some (shiftErase L n) := by rfl

theorem shiftErase_empty (L : List Symbol) :
    step unaryShift (shiftErase L 0) = some (shiftEnd L 0) := by rfl

theorem shiftErase_nonempty (L : List Symbol) (n : Nat) :
    step unaryShift (shiftErase L (n + 1)) = some (shiftScan L 0 n) := by rfl

theorem shiftScan_next (L : List Symbol) (seen remaining : Nat) :
    step unaryShift (shiftScan L seen (remaining + 1)) =
      some (shiftScan L (seen + 1) remaining) := by
  simp [unaryShift, shiftScan, step, instruction, symbolIndex, perform, moveRight,
    List.replicate_succ]

theorem shiftScan_last (L : List Symbol) (seen : Nat) :
    step unaryShift (shiftScan L seen 0) = some (shiftEnd L (seen + 1)) := by
  simp [unaryShift, shiftScan, shiftEnd, step, instruction, symbolIndex, perform, moveRight,
    List.replicate_succ]

theorem shiftScan_reaches (L : List Symbol) (seen remaining : Nat) :
    Reaches unaryShift (shiftScan L seen remaining) (shiftEnd L (seen + remaining + 1)) := by
  induction remaining generalizing seen with
  | zero => simpa using Reaches.step (shiftScan_last L seen) (Reaches.refl _)
  | succ remaining ih =>
    have h := Reaches.step (shiftScan_next L seen remaining) (ih (seen + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem shiftEnd_next (L : List Symbol) (seen : Nat) :
    step unaryShift (shiftEnd L seen) = some (shiftWritten L seen) := by rfl

theorem shiftWritten_empty (L : List Symbol) :
    step unaryShift (shiftWritten L 0) = some (shiftGap L 0) := by rfl

theorem shiftWritten_nonempty (L : List Symbol) (n : Nat) :
    step unaryShift (shiftWritten L (n + 1)) = some (shiftReturn L n 1) := by
  simp [unaryShift, shiftWritten, shiftReturn, step, instruction, symbolIndex, perform, moveLeft,
    List.replicate_succ]

theorem shiftReturn_next (L : List Symbol) (left right : Nat) :
    step unaryShift (shiftReturn L (left + 1) right) = some (shiftReturn L left (right + 1)) := by
  simp [unaryShift, shiftReturn, step, instruction, symbolIndex, perform, moveLeft,
    List.replicate_succ]

theorem shiftReturn_last (L : List Symbol) (right : Nat) :
    step unaryShift (shiftReturn L 0 right) = some (shiftGap L right) := by
  simp [unaryShift, shiftReturn, shiftGap, step, instruction, symbolIndex, perform, moveLeft,
    List.replicate_succ]

theorem shiftReturn_reaches (L : List Symbol) (left right : Nat) :
    Reaches unaryShift (shiftReturn L left right) (shiftGap L (left + right)) := by
  induction left generalizing right with
  | zero => simpa using Reaches.step (shiftReturn_last L right) (Reaches.refl _)
  | succ left ih =>
    have h := Reaches.step (shiftReturn_next L left right) (ih (right + 1))
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem shiftGap_halts (L : List Symbol) (n : Nat) : Halted unaryShift (shiftGap L n) := by rfl

theorem shiftStart_reaches (L : List Symbol) (n : Nat) :
    Reaches unaryShift (shiftStart L n) (shiftGap L n) := by
  apply reaches_trans (b := shiftErase L n)
  · exact .step (shiftStart_next L n) (.refl _)
  · cases n with
    | zero =>
      exact .step (shiftErase_empty L) (.step (shiftEnd_next L 0)
        (.step (shiftWritten_empty L) (.refl _)))
    | succ n =>
      apply reaches_trans (b := shiftEnd L (n + 1))
      · exact .step (shiftErase_nonempty L n) (by simpa using shiftScan_reaches L 0 n)
      · exact .step (shiftEnd_next L (n + 1))
          (.step (shiftWritten_nonempty L n) (by simpa using shiftReturn_reaches L n 1))

#print axioms shiftStart_reaches
#print axioms shiftGap_halts
end LambdaTuring.Machine
