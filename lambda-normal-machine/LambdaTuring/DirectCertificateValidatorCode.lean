/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectCertificateValidation
public meta import LambdaTuring.DirectCertificateValidation

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

def boolFlag (p : Bool) : Nat := if p then 1 else 0

def listValidHeadRep := liftLeftRep (liftPredRep liftKeyRep)
def listValidTailRep := liftRightRep (liftPredRep liftKeyRep)
def listValidReadRep := LiftStepRep.lookup liftKeyRep listValidTailRep

def listValidStepRep (test : Code) (p : Nat → Bool)
    (htest : ∀ n, test.eval n = Part.some (boolFlag (p n))) :=
  liftKeyRep.select betaOneRep
    (((listValidHeadRep.map test (fun n => boolFlag (p n)) htest)).select betaZeroRep listValidReadRep)

def listValidHeadCode : Code := .comp .left (.comp predCode liftKeyCode)
def listValidTailCode : Code := .comp .right (.comp predCode liftKeyCode)
def listValidReadCode : Code := .comp historyLookupCode
  (.pair (.pair liftKeyCode listValidTailCode) liftHistoryCode)
def listValidStepCode (test : Code) : Code := chooseZeroCode liftKeyCode (.comp .succ .zero)
  (chooseZeroCode (.comp test listValidHeadCode) .zero listValidReadCode)
def listValidCode (test : Code) : Code :=
  .comp (courseCode (listValidStepCode test)) (.pair .zero Code.id)

theorem listValidStepRep_code (test : Code) (p : Nat → Bool)
    (htest : ∀ n, test.eval n = Part.some (boolFlag (p n))) :
    (listValidStepRep test p htest).code = listValidStepCode test := rfl

def listValidStepValue (p : Nat → Bool) (key : Nat) (history : List Nat) : Nat :=
  if key = 0 then 1 else if p key.pred.unpair.1 then
    (history[key.pred - key.pred.unpair.2]?).getD 0 else 0

theorem listValidStepCode_eval (test : Code) (p : Nat → Bool)
    (htest : ∀ n, test.eval n = Part.some (boolFlag (p n)))
    (context key : Nat) (history : List Nat) :
    (listValidStepCode test).eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (listValidStepValue p key history) := by
  have h := (listValidStepRep test p htest).sound context key history
  rw [listValidStepRep_code] at h
  change (listValidStepCode test).eval (Nat.pair context (Nat.pair key (Encodable.encode history))) =
      Part.some (if key = 0 then 1 else if boolFlag (p key.pred.unpair.1) = 0 then 0 else
        (history[key.pred - key.pred.unpair.2]?).getD 0) at h
  cases hp : p key.pred.unpair.1 <;>
    simp only [Nat.pred_eq_sub_one] at hp <;>
    simpa [listValidStepValue, boolFlag, hp] using h

theorem listValidCode_eval (test : Code) (p : Nat → Bool)
    (htest : ∀ n, test.eval n = Part.some (boolFlag (p n))) (n : Nat) :
    (listValidCode test).eval n = Part.some (boolFlag (encodedListValid p n)) := by
  let f : Nat → Nat → Nat := fun _ k => boolFlag (encodedListValid p k)
  have hstep : ∀ context key,
      (listValidStepCode test).eval (Nat.pair context
        (Nat.pair key (Encodable.encode (courseHistory f context key)))) = Part.some (f context key) := by
    intro context key
    rw [listValidStepCode_eval test p htest]
    cases key with
    | zero => simp [listValidStepValue, f, encodedListValid, boolFlag]
    | succ k =>
      have hlt : k.unpair.2 < k + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le k)
      have hr := courseHistory_lookup f context (k + 1) k.unpair.2 hlt
      simp only [Nat.add_sub_cancel, f, boolFlag] at hr
      simp [listValidStepValue, encodedListValid, f, boolFlag, hr]
      split_ifs <;> simp_all
  have hz : Code.eval .zero n = Part.some 0 := rfl
  have hp := evalPairSome .zero Code.id n 0 n hz (Code.eval_id n)
  have hc := courseCode_eval (listValidStepCode test) f hstep 0 n
  exact evalCompSome (courseCode (listValidStepCode test)) (.pair .zero Code.id) _ _ _ hp hc

def encodedBoolValidCode : Code := chooseZeroCode (.comp predCode Code.id)
  (.comp .succ .zero) .zero
def encodedPathValidCode : Code := listValidCode encodedBoolValidCode
def encodedCertificateValidCode : Code := listValidCode encodedPathValidCode

theorem encodedBoolValidCode_eval (n : Nat) :
    encodedBoolValidCode.eval n = Part.some (boolFlag (encodedBoolValid n)) := by
  have hid := Code.eval_id n
  have hp := evalCompSome predCode Code.id _ _ _ hid (eval_predCode n)
  have hz : Code.eval .zero n = Part.some 0 := rfl
  have ho := evalCompSome .succ .zero _ _ _ hz (show Code.eval .succ 0 = Part.some 1 from rfl)
  have h := chooseZeroCode_eval (.comp predCode Code.id) (.comp .succ .zero) .zero
    _ _ _ _ hp ho hz
  simp only [encodedBoolValidCode, encodedBoolValid, boolFlag, decide_eq_true_eq, Nat.pred_eq_sub_one] at *
  split_ifs at h ⊢ <;> simp_all <;> omega

theorem encodedPathValidCode_eval (n : Nat) :
    encodedPathValidCode.eval n = Part.some (boolFlag (encodedPathValid n)) :=
  listValidCode_eval encodedBoolValidCode encodedBoolValid encodedBoolValidCode_eval n

theorem encodedCertificateValidCode_eval (n : Nat) :
    encodedCertificateValidCode.eval n = Part.some (boolFlag (encodedCertificateValid n)) :=
  listValidCode_eval encodedPathValidCode encodedPathValid encodedPathValidCode_eval n

#print axioms encodedCertificateValidCode
#print axioms encodedCertificateValidCode_eval
end LambdaTuring
