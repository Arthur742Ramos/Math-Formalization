/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FastPpred
public meta import LambdaTuring.FastPpred
public import Mathlib.Logic.Equiv.List

@[expose] public section

namespace LambdaTuring.EffectiveCode
open Nat.Partrec

/-- These programs operate on the actual Mathlib natural-number list encoding. -/
def listConsCode : Code := .succ
def listHeadCode : Code := .comp .left predCode
def listTailCode : Code := .comp .right predCode

theorem eval_listConsCode (a xs : Nat) :
    listConsCode.eval (Nat.pair a xs) = Part.some (Nat.succ (Nat.pair a xs)) := rfl

theorem eval_listHeadCode (n : Nat) :
    listHeadCode.eval n = Part.some n.pred.unpair.1 := by
  change (predCode.eval n).bind (fun x => Code.eval .left x) = _
  rw [eval_predCode, Part.bind_some]
  rfl

theorem eval_listTailCode (n : Nat) :
    listTailCode.eval n = Part.some n.pred.unpair.2 := by
  change (predCode.eval n).bind (fun x => Code.eval .right x) = _
  rw [eval_predCode, Part.bind_some]
  rfl

theorem listCons_encoded {α : Type} [Encodable α] (a : α) (xs : List α) :
    listConsCode.eval (Nat.pair (Encodable.encode a) (Encodable.encode xs)) =
      Part.some (Encodable.encode (a :: xs)) := by
  rw [eval_listConsCode, Encodable.encode_list_cons]

theorem listHead_encoded {α : Type} [Encodable α] (a : α) (xs : List α) :
    listHeadCode.eval (Encodable.encode (a :: xs)) = Part.some (Encodable.encode a) := by
  rw [eval_listHeadCode, Encodable.encode_list_cons]
  simp

theorem listTail_encoded {α : Type} [Encodable α] (a : α) (xs : List α) :
    listTailCode.eval (Encodable.encode (a :: xs)) = Part.some (Encodable.encode xs) := by
  rw [eval_listTailCode, Encodable.encode_list_cons]
  simp

theorem listHead_empty {α : Type} [Encodable α] :
    listHeadCode.eval (Encodable.encode ([] : List α)) = Part.some 0 := by
  simp [eval_listHeadCode]

theorem listTail_empty {α : Type} [Encodable α] :
    listTailCode.eval (Encodable.encode ([] : List α)) = Part.some 0 := by
  simp [eval_listTailCode]

#print axioms listConsCode
#print axioms listHeadCode
#print axioms listTailCode
#print axioms listHead_encoded
#print axioms listTail_encoded
end LambdaTuring.EffectiveCode
