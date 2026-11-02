/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Basic
public meta import LambdaTuring.Basic

@[expose] public section

/-! A concrete example of a terminating nonnumerical lambda observation. -/
namespace LambdaTuring

def identityTerm : Term := .abs (.var 0)

def discardInput : Term := .abs identityTerm

theorem identity_no_beta : ¬ ∃ t, Beta identityTerm t := by
  rintro ⟨_, h⟩
  cases h with
  | abs h => cases h

theorem discard_step (n : Nat) {t : Term} :
    Beta (.app discardInput (church n)) t → t = identityTerm := by
  intro h
  cases h with
  | contract => rfl
  | appLeft h =>
    cases h with
    | abs h => exact False.elim (identity_no_beta ⟨_, h⟩)
  | appRight h => exact False.elim (church_no_beta n ⟨_, h⟩)

theorem identity_not_church (n : Nat) : identityTerm ≠ church n := by
  simp [identityTerm, church]


theorem discard_reaches_identity (n : Nat) :
    Reaches (.app discardInput (church n)) identityTerm := by
  apply Reaches.step (b := identityTerm)
  · exact Beta.contract _ _
  · exact .refl _
theorem discard_no_numeral (n m : Nat) :
    ¬ Reaches (.app discardInput (church n)) (church m) := by
  intro h
  cases h with
  | step h rest =>
    have eq := discard_step n h
    subst_vars
    exact identity_not_church m (normal_reaches_eq identity_no_beta rest)

#print axioms discard_no_numeral

end LambdaTuring
