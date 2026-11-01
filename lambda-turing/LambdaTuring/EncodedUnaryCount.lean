/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedUnaryUpdate
public meta import LambdaTuring.EncodedUnaryUpdate

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

def unaryContextCode : Code := .left
def unaryCounterCode : Code := .comp .left .right
def unaryPriorCode : Code := .comp .right .right
def unaryIndexCode : Code := .comp subPairCode (.pair unaryContextCode (.comp .succ unaryCounterCode))
def unaryLookupCode : Code := .comp listLookupCode (.pair unaryContextCode unaryIndexCode)
def unaryFoldStepCode : Code := .comp unaryUpdateCode (.pair unaryLookupCode unaryPriorCode)
def unaryFoldCode : Code := .prec (Code.const 1) unaryFoldStepCode
def unaryCountCode : Code := .comp unaryFoldCode (.pair Code.id Code.id)

theorem unaryFoldStepCode_eval (xs suffix : List Symbol) (k : Nat) :
    unaryFoldStepCode.eval (Nat.pair (Encodable.encode xs)
      (Nat.pair k (Encodable.encode (unaryCount suffix)))) =
      Part.some (Encodable.encode (unaryCount (xs[Encodable.encode xs - (k + 1)]?.toList ++ suffix))) := by
  let bound := Encodable.encode xs
  let prior := Encodable.encode (unaryCount suffix)
  let input := Nat.pair bound (Nat.pair k prior)
  have hctx : unaryContextCode.eval input = Part.some bound := by simp [input, unaryContextCode, Code.eval]
  have hright : Code.eval .right input = Part.some (Nat.pair k prior) := by simp [input, Code.eval]
  have hleft : Code.eval .left (Nat.pair k prior) = Part.some k := by simp [Code.eval]
  have hright' : Code.eval .right (Nat.pair k prior) = Part.some prior := by simp [Code.eval]
  have hk := evalCompSome .left .right _ _ _ hright hleft
  have hp := evalCompSome .right .right _ _ _ hright hright'
  have hsucc := evalCompSome .succ unaryCounterCode _ _ _ hk
    (show Code.eval .succ k = Part.some (k + 1) from rfl)
  have hsubInput := evalPairSome unaryContextCode (.comp .succ unaryCounterCode) _ _ _ hctx hsucc
  have hidx := evalCompSome subPairCode _ _ _ _ hsubInput (subPairCode_eval bound (k + 1))
  have hlookupInput := evalPairSome unaryContextCode unaryIndexCode _ _ _ hctx hidx
  have hlookup := evalCompSome listLookupCode _ _ _ _ hlookupInput
    (listLookupCode_eval xs (bound - (k + 1)))
  have hupdateInput := evalPairSome unaryLookupCode unaryPriorCode _ _ _ hlookup hp
  have hresult := evalCompSome unaryUpdateCode _ _ _ _ hupdateInput
    (unaryUpdateCode_optional (xs[bound - (k + 1)]?) suffix)
  exact hresult

theorem unaryFoldCode_eval (xs : List Symbol) (k : Nat) (hk : k ≤ Encodable.encode xs) :
    unaryFoldCode.eval (Nat.pair (Encodable.encode xs) k) =
      Part.some (Encodable.encode (unaryCount (xs.drop (Encodable.encode xs - k)))) := by
  induction k with
  | zero =>
    rw [unaryFoldCode, Code.eval_prec_zero]
    have hdrop : xs.drop (Encodable.encode xs) = [] :=
      List.drop_of_length_le (Encodable.length_le_encode xs)
    simp [hdrop, unaryCount, Code.eval_const]
  | succ k ih =>
    have hle : k ≤ Encodable.encode xs := by omega
    have heq : Encodable.encode xs - k = (Encodable.encode xs - (k + 1)) + 1 := by omega
    have hdrop : xs.drop (Encodable.encode xs - (k + 1)) =
        xs[Encodable.encode xs - (k + 1)]?.toList ++ xs.drop (Encodable.encode xs - k) := by
      rw [List.drop_eq_getElem?_toList_append, heq]
    rw [unaryFoldCode, Code.eval_prec_succ]
    change (Code.eval unaryFoldCode (Nat.pair (Encodable.encode xs) k)).bind _ = _
    rw [ih hle]
    change (Part.some (Encodable.encode (unaryCount (xs.drop (Encodable.encode xs - k))))).bind
      (fun z => unaryFoldStepCode.eval (Nat.pair (Encodable.encode xs) (Nat.pair k z))) = _
    rw [Part.bind_some, unaryFoldStepCode_eval, hdrop]

theorem unaryCountCode_eval (xs : List Symbol) :
    unaryCountCode.eval (Encodable.encode xs) = Part.some (Encodable.encode (unaryCount xs)) := by
  have hp := evalPairSome Code.id Code.id _ _ _ (Code.eval_id (Encodable.encode xs))
    (Code.eval_id (Encodable.encode xs))
  have h := evalCompSome unaryFoldCode _ _ _ _ hp
    (unaryFoldCode_eval xs (Encodable.encode xs) (Nat.le_refl _))
  simpa [unaryCountCode] using h

def decodeCode : Code := .comp predCode unaryCountCode

theorem decodeCode_eval (xs : List Symbol) :
    decodeCode.eval (Encodable.encode xs) = Part.some (Encodable.encode (decode xs)) := by
  have h := evalCompSome predCode unaryCountCode _ _ _ (unaryCountCode_eval xs)
    (eval_predCode (Encodable.encode (unaryCount xs)))
  cases hc : unaryCount xs with
  | none => simpa [decodeCode, decode, hc] using h
  | some n => cases n <;> simpa [decodeCode, decode, hc] using h

#print axioms unaryCountCode
#print axioms unaryCountCode_eval
#print axioms decodeCode
#print axioms decodeCode_eval
end LambdaTuring.Machine
