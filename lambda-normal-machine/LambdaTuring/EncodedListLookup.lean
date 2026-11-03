/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedTapeAction
public meta import LambdaTuring.EncodedTapeAction

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

theorem listTail_any {α : Type} [Encodable α] (xs : List α) :
    listTailCode.eval (Encodable.encode xs) = Part.some (Encodable.encode xs.tail) := by
  cases xs with
  | nil => simpa using (listTail_empty (α := α))
  | cons a xs => simpa using listTail_encoded a xs

def listDropCode : Code := .prec Code.id (.comp listTailCode (.comp .right .right))

theorem listDropCode_eval {α : Type} [Encodable α] (xs : List α) (n : Nat) :
    listDropCode.eval (Nat.pair (Encodable.encode xs) n) = Part.some (Encodable.encode (xs.drop n)) := by
  induction n with
  | zero =>
    rw [listDropCode, Code.eval_prec_zero]
    simp
  | succ n ih =>
    rw [listDropCode, Code.eval_prec_succ]
    change (Code.eval listDropCode (Nat.pair (Encodable.encode xs) n)).bind _ = _
    rw [ih]
    change (Part.some (Encodable.encode (xs.drop n))).bind
      (fun z => Code.eval (.comp listTailCode (.comp .right .right))
        (Nat.pair (Encodable.encode xs) (Nat.pair n z))) = _
    rw [Part.bind_some]
    have hproj : Code.eval (.comp .right .right)
        (Nat.pair (Encodable.encode xs) (Nat.pair n (Encodable.encode (xs.drop n)))) =
          Part.some (Encodable.encode (xs.drop n)) := by
      change (Code.eval .right _).bind (fun z => Code.eval .right z) = _
      simp [Code.eval, Part.bind_some]
    have h := evalCompSome listTailCode (.comp .right .right) _ _ _ hproj (listTail_any (xs.drop n))
    simpa [List.tail_drop] using h

def listHeadOptionCode : Code := chooseZeroCode Code.id .zero (.comp .succ listHeadCode)
def listLookupCode : Code := .comp listHeadOptionCode listDropCode

theorem listHeadOptionCode_eval {α : Type} [Encodable α] (xs : List α) :
    listHeadOptionCode.eval (Encodable.encode xs) = Part.some (Encodable.encode xs.head?) := by
  cases xs with
  | nil =>
    have ht := Code.eval_id (Encodable.encode ([] : List α))
    have ha : Code.eval .zero (Encodable.encode ([] : List α)) = Part.some 0 := rfl
    have hb := evalCompSome .succ listHeadCode _ _ _ (listHead_empty (α := α)) (show Code.eval .succ 0 = Part.some 1 from rfl)
    have h := chooseZeroCode_eval Code.id .zero (.comp .succ listHeadCode) _ _ _ _ ht ha hb
    simpa [listHeadOptionCode, Code.eval] using h
  | cons a xs =>
    have ht := Code.eval_id (Encodable.encode (a :: xs))
    have ha : Code.eval .zero (Encodable.encode (a :: xs)) = Part.some 0 := rfl
    have hb := evalCompSome .succ listHeadCode _ _ _ (listHead_encoded a xs)
      (show Code.eval .succ (Encodable.encode a) = Part.some (Nat.succ (Encodable.encode a)) from rfl)
    have h := chooseZeroCode_eval Code.id .zero (.comp .succ listHeadCode) _ _ _ _ ht ha hb
    simpa [listHeadOptionCode, Encodable.encode_list_cons] using h

theorem listLookupCode_eval {α : Type} [Encodable α] (xs : List α) (n : Nat) :
    listLookupCode.eval (Nat.pair (Encodable.encode xs) n) =
      Part.some (Encodable.encode xs[n]?) := by
  have h := evalCompSome listHeadOptionCode listDropCode _ _ _
    (listDropCode_eval xs n) (listHeadOptionCode_eval (xs.drop n))
  simpa [listLookupCode] using h

/-- Missing list entries and explicit `none` entries both encode as `none`. -/
def listLookupFlattenCode : Code := .comp predCode listLookupCode

theorem listLookupFlattenCode_eval {α : Type} [Encodable α] (xs : List (Option α)) (n : Nat) :
    listLookupFlattenCode.eval (Nat.pair (Encodable.encode xs) n) =
      Part.some (Encodable.encode ((xs[n]?).getD none)) := by
  have h := evalCompSome predCode listLookupCode _ _ _
    (listLookupCode_eval xs n) (eval_predCode (Encodable.encode xs[n]?))
  cases he : xs[n]? with
  | none => simpa [listLookupFlattenCode, he] using h
  | some v => simpa [listLookupFlattenCode, he] using h

#print axioms listDropCode
#print axioms listLookupCode
#print axioms listLookupFlattenCode
#print axioms listLookupCode_eval
#print axioms listLookupFlattenCode_eval
end LambdaTuring.Machine
