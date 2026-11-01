/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedMachineEvaluator
public meta import LambdaTuring.EncodedMachineEvaluator

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

/-- A direct, data-only encoding with strictly smaller proper subterms. -/
def directTermNumber : Term → Nat
  | .var n => Nat.succ (Nat.pair 0 n)
  | .abs body => Nat.succ (Nat.pair 1 (directTermNumber body))
  | .app f x => Nat.succ (Nat.pair 2 (Nat.pair (directTermNumber f) (directTermNumber x)))

theorem directTermNumber_injective : Function.Injective directTermNumber := by
  intro a b h
  induction a generalizing b with
  | var n =>
    cases b <;> simp [directTermNumber] at h ⊢
    exact h
  | abs a ih =>
    cases b with
    | var n => simp [directTermNumber] at h
    | abs b =>
      simp only [directTermNumber, Nat.succ.injEq, Nat.pair_eq_pair, true_and] at h
      exact congrArg Term.abs (ih h)
    | app f x => simp [directTermNumber] at h
  | app f x ihf ihx =>
    cases b with
    | var n => simp [directTermNumber] at h
    | abs b => simp [directTermNumber] at h
    | app g y =>
      simp only [directTermNumber, Nat.succ.injEq, Nat.pair_eq_pair, true_and] at h
      exact congrArg₂ Term.app (ihf h.1) (ihx h.2)

theorem directTermNumber_abs_lt (t : Term) : directTermNumber t < directTermNumber (.abs t) := by
  have h := Nat.right_le_pair 1 (directTermNumber t)
  simp only [directTermNumber]
  omega

theorem directTermNumber_app_left_lt (f x : Term) :
    directTermNumber f < directTermNumber (.app f x) := by
  have h₁ := Nat.left_le_pair (directTermNumber f) (directTermNumber x)
  have h₂ := Nat.right_le_pair 2 (Nat.pair (directTermNumber f) (directTermNumber x))
  simp only [directTermNumber]
  omega

theorem directTermNumber_app_right_lt (f x : Term) :
    directTermNumber x < directTermNumber (.app f x) := by
  have h₁ := Nat.right_le_pair (directTermNumber f) (directTermNumber x)
  have h₂ := Nat.right_le_pair 2 (Nat.pair (directTermNumber f) (directTermNumber x))
  simp only [directTermNumber]
  omega

def directTaggedCode (tag : Nat) : Code := .comp .succ (.pair (Code.const tag) Code.id)
def directVarCode : Code := directTaggedCode 0
def directAbsCode : Code := directTaggedCode 1
def directAppCode : Code := directTaggedCode 2
def directTagCode : Code := .comp .left predCode
def directPayloadCode : Code := .comp .right predCode

theorem directTaggedCode_eval (tag payload : Nat) :
    (directTaggedCode tag).eval payload = Part.some (Nat.succ (Nat.pair tag payload)) := by
  have hpair := evalPairSome (Code.const tag) Code.id payload tag payload
    (Code.eval_const tag payload) (Code.eval_id payload)
  exact evalCompSome .succ _ _ _ _ hpair (show Code.eval .succ (Nat.pair tag payload) = _ from rfl)

theorem directVarCode_eval (n : Nat) : directVarCode.eval n = Part.some (directTermNumber (.var n)) :=
  directTaggedCode_eval 0 n

theorem directAbsCode_eval (t : Term) :
    directAbsCode.eval (directTermNumber t) = Part.some (directTermNumber (.abs t)) :=
  directTaggedCode_eval 1 (directTermNumber t)

theorem directAppCode_eval (f x : Term) :
    directAppCode.eval (Nat.pair (directTermNumber f) (directTermNumber x)) =
      Part.some (directTermNumber (.app f x)) :=
  directTaggedCode_eval 2 _

theorem directTagCode_eval (tag payload : Nat) :
    directTagCode.eval (Nat.succ (Nat.pair tag payload)) = Part.some tag := by
  have h := evalCompSome .left predCode _ _ _ (eval_predCode (Nat.succ (Nat.pair tag payload)))
    (show Code.eval .left (Nat.pair tag payload) = Part.some tag by simp [Code.eval])
  exact h

theorem directPayloadCode_eval (tag payload : Nat) :
    directPayloadCode.eval (Nat.succ (Nat.pair tag payload)) = Part.some payload := by
  have h := evalCompSome .right predCode _ _ _ (eval_predCode (Nat.succ (Nat.pair tag payload)))
    (show Code.eval .right (Nat.pair tag payload) = Part.some payload by simp [Code.eval])
  exact h

#print axioms directTermNumber
#print axioms directVarCode
#print axioms directAbsCode
#print axioms directAppCode
#print axioms directTermNumber_injective
end LambdaTuring
