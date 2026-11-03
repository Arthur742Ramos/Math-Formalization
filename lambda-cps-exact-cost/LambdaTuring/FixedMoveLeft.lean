/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FiniteTable
public meta import LambdaTuring.FiniteTable
public import Mathlib.Logic.Function.Iterate

@[expose] public section

namespace LambdaTuring.Machine

def leftMoveInstruction (n : Nat) (q : Fin (n + 1)) (_ : Symbol) : Option (Fin (n + 1) × Action) := by
  if h : q.val < n then exact some (⟨q.val + 1, by omega⟩, .left) else exact none

def fixedMoveLeft (n : Nat) : Program n := tableOfFunction (leftMoveInstruction n)

def leftMoveConfig (n i : Nat) (h : i ≤ n) (t : Tape) : Config n := ⟨⟨i, by omega⟩, t⟩

theorem fixedMoveLeft_step (n i : Nat) (h : i < n) (t : Tape) :
    step (fixedMoveLeft n) (leftMoveConfig n i (by omega) t) =
      some (leftMoveConfig n (i + 1) (by omega) (moveLeft t)) := by
  simp [step, fixedMoveLeft, tableOfFunction_instruction, leftMoveConfig, leftMoveInstruction, h, perform]

theorem fixedMoveLeft_aux (n d i : Nat) (h : i + d = n) (t : Tape) :
    Reaches (fixedMoveLeft n) (leftMoveConfig n i (by omega) t)
      (leftMoveConfig n n (by omega) ((moveLeft^[d]) t)) := by
  induction d generalizing i t with
  | zero =>
    have : i = n := by omega
    subst i
    simpa using Reaches.refl (leftMoveConfig n n (by omega) t)
  | succ d ih =>
    have hs := fixedMoveLeft_step n i (by omega) t
    apply Reaches.step hs
    simpa [Function.iterate_succ_apply] using ih (i + 1) (by omega) (moveLeft t)

theorem fixedMoveLeft_reaches (n i : Nat) (h : i ≤ n) (t : Tape) :
    Reaches (fixedMoveLeft n) (leftMoveConfig n i h t)
      (leftMoveConfig n n (by omega) ((moveLeft^[n - i]) t)) := by
  exact fixedMoveLeft_aux n (n - i) i (by omega) t

theorem fixedMoveLeft_halts (n : Nat) (t : Tape) :
    Halted (fixedMoveLeft n) (leftMoveConfig n n (by omega) t) := by
  simp [Halted, step, fixedMoveLeft, tableOfFunction_instruction, leftMoveConfig, leftMoveInstruction]

#print axioms fixedMoveLeft_reaches
#print axioms fixedMoveLeft_halts
end LambdaTuring.Machine
