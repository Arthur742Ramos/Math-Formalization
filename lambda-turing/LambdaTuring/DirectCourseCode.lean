/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectChurchDecode
public meta import LambdaTuring.DirectChurchDecode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec
open LambdaTuring.Machine
open LambdaTuring.EffectiveCode

/-- Previous results in reverse index order, used for course-of-values recursion. -/
def courseHistory (f : Nat → Nat → Nat) (context : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => f context k :: courseHistory f context k

/-- `step` receives a context, an index, and the encoded history. -/
def courseFoldStepCode (step : Code) : Code :=
  .comp listConsCode (.pair step (.comp .right .right))
def courseFoldCode (step : Code) : Code := .prec .zero (courseFoldStepCode step)
def courseCode (step : Code) : Code :=
  .comp listHeadCode (.comp (courseFoldCode step) (.pair .left (.comp .succ .right)))

theorem courseFoldCode_eval (step : Code) (f : Nat → Nat → Nat)
    (hstep : ∀ context k, step.eval (Nat.pair context (Nat.pair k (Encodable.encode (courseHistory f context k)))) =
      Part.some (f context k)) (context n : Nat) :
    (courseFoldCode step).eval (Nat.pair context n) = Part.some (Encodable.encode (courseHistory f context n)) := by
  induction n with
  | zero => rw [courseFoldCode, Code.eval_prec_zero]; rfl
  | succ n ih =>
    rw [courseFoldCode, Code.eval_prec_succ]
    change ((courseFoldCode step).eval (Nat.pair context n)).bind _ = _
    rw [ih]
    change (Part.some (Encodable.encode (courseHistory f context n))).bind
      (fun z => (courseFoldStepCode step).eval (Nat.pair context (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hproject : Code.eval (.comp .right .right)
        (Nat.pair context (Nat.pair n (Encodable.encode (courseHistory f context n)))) =
        Part.some (Encodable.encode (courseHistory f context n)) := by
      change (Code.eval .right _).bind (fun x => Code.eval .right x) = _
      simp [Code.eval, Part.bind_some]
    have hpair := evalPairSome step (.comp .right .right) _ _ _ (hstep context n) hproject
    have h := evalCompSome listConsCode _ _ _ _ hpair (listCons_encoded (f context n) (courseHistory f context n))
    simpa [courseFoldStepCode, courseHistory] using h

theorem courseCode_eval (step : Code) (f : Nat → Nat → Nat)
    (hstep : ∀ context k, step.eval (Nat.pair context (Nat.pair k (Encodable.encode (courseHistory f context k)))) =
      Part.some (f context k)) (context n : Nat) :
    (courseCode step).eval (Nat.pair context n) = Part.some (f context n) := by
  let input := Nat.pair context n
  have hl : Code.eval .left input = Part.some context := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some n := by simp [input, Code.eval]
  have hs := evalCompSome .succ .right _ _ _ hr (show Code.eval .succ n = Part.some (n + 1) from rfl)
  have hp := evalPairSome .left (.comp .succ .right) _ _ _ hl hs
  have hfold := evalCompSome (courseFoldCode step) _ _ _ _ hp (courseFoldCode_eval step f hstep context (n + 1))
  have hhead := listHead_encoded (f context n) (courseHistory f context n)
  have h := evalCompSome listHeadCode _ _ _ _ hfold hhead
  exact h

theorem courseHistory_lookup (f : Nat → Nat → Nat) (context k j : Nat) (hj : j < k) :
    (courseHistory f context k)[k - 1 - j]? = some (f context j) := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : j = k
    · subst j
      simp [courseHistory]
    · have hjk : j < k := by omega
      have hd : k - j = (k - 1 - j) + 1 := by omega
      change (f context k :: courseHistory f context k)[k - j]? = _
      rw [hd, List.getElem?_cons_succ]
      exact ih hjk

def historyIndexCode : Code :=
  .comp subPairCode (.pair (.comp predCode (.comp .left .left)) (.comp .right .left))
def historyLookupCode : Code :=
  .comp predCode (.comp listLookupCode (.pair .right historyIndexCode))

theorem historyLookupCode_eval (f : Nat → Nat → Nat) (context k j : Nat) (hj : j < k) :
    historyLookupCode.eval (Nat.pair (Nat.pair k j) (Encodable.encode (courseHistory f context k))) =
      Part.some (f context j) := by
  let hist := courseHistory f context k
  let input := Nat.pair (Nat.pair k j) (Encodable.encode hist)
  have hl : Code.eval .left input = Part.some (Nat.pair k j) := by simp [input, Code.eval]
  have hr : Code.eval .right input = Part.some (Encodable.encode hist) := by simp [input, Code.eval]
  have hk' : Code.eval .left (Nat.pair k j) = Part.some k := by simp [Code.eval]
  have hj' : Code.eval .right (Nat.pair k j) = Part.some j := by simp [Code.eval]
  have hk := evalCompSome .left .left _ _ _ hl hk'
  have hjcode := evalCompSome .right .left _ _ _ hl hj'
  have hpred := evalCompSome predCode (.comp .left .left) _ _ _ hk (eval_predCode k)
  have hindexInput := evalPairSome (.comp predCode (.comp .left .left)) (.comp .right .left) _ _ _ hpred hjcode
  have hindex := evalCompSome subPairCode _ _ _ _ hindexInput (subPairCode_eval k.pred j)
  have hlookupInput := evalPairSome .right historyIndexCode _ _ _ hr hindex
  have hlookup := evalCompSome listLookupCode _ _ _ _ hlookupInput (listLookupCode_eval hist (k.pred - j))
  have hvalue := evalCompSome predCode _ _ _ _ hlookup (eval_predCode (Encodable.encode hist[k.pred - j]?))
  have hmem : hist[k.pred - j]? = some (f context j) := by
    simpa [hist, Nat.pred_eq_sub_one] using courseHistory_lookup f context k j hj
  rw [hmem] at hvalue
  simpa [historyLookupCode, historyIndexCode, input, hist] using hvalue

#print axioms courseCode
#print axioms courseCode_eval
#print axioms historyLookupCode
#print axioms historyLookupCode_eval
end LambdaTuring
