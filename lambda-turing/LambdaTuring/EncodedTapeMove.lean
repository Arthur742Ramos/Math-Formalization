/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedSymbolCode
public meta import LambdaTuring.EncodedSymbolCode

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

theorem evalPairSome (f g : Code) (n a b : Nat)
    (hf : f.eval n = Part.some a) (hg : g.eval n = Part.some b) :
    (Code.pair f g).eval n = Part.some (Nat.pair a b) := by
  change Nat.pair <$> f.eval n <*> g.eval n = _
  simp [hf, hg, Seq.seq]

theorem evalCompSome (f g : Code) (n a b : Nat)
    (hg : g.eval n = Part.some a) (hf : f.eval a = Part.some b) :
    (Code.comp f g).eval n = Part.some b := by
  change (g.eval n).bind (fun x => f.eval x) = _
  rw [hg, Part.bind_some, hf]

theorem listHead_symbol (xs : List Symbol) :
    listHeadCode.eval (Encodable.encode xs) =
      Part.some (Encodable.encode (xs.head?.getD .blank)) := by
  cases xs with
  | nil => simpa [symbol_encoded, symbolIndex] using (listHead_empty (α := Symbol))
  | cons a xs => simpa using listHead_encoded a xs

theorem listTail_symbol (xs : List Symbol) :
    listTailCode.eval (Encodable.encode xs) = Part.some (Encodable.encode xs.tail) := by
  cases xs with
  | nil => simpa using (listTail_empty (α := Symbol))
  | cons a xs => simpa using listTail_encoded a xs

def tapeMoveLeftCode : Code :=
  .pair (.comp listTailCode tapeLeftCode)
    (.pair (.comp listHeadCode tapeLeftCode)
      (.comp listConsCode (.pair tapeHeadCode tapeRightCode)))

def tapeMoveRightCode : Code :=
  .pair (.comp listConsCode (.pair tapeHeadCode tapeLeftCode))
    (.pair (.comp listHeadCode tapeRightCode) (.comp listTailCode tapeRightCode))

def tapeWriteCode : Code :=
  .pair (.comp tapeLeftCode .right) (.pair .left (.comp tapeRightCode .right))

theorem tapeMoveLeftCode_eval (t : Tape) :
    tapeMoveLeftCode.eval (Encodable.encode t) = Part.some (Encodable.encode (moveLeft t)) := by
  have hleft := evalCompSome listTailCode tapeLeftCode _ _ _
    (tapeLeftCode_eval t) (listTail_symbol t.left)
  have hhead := evalCompSome listHeadCode tapeLeftCode _ _ _
    (tapeLeftCode_eval t) (listHead_symbol t.left)
  have hpair := evalPairSome tapeHeadCode tapeRightCode _ _ _
    (tapeHeadCode_eval t) (tapeRightCode_eval t)
  have hright := evalCompSome listConsCode (Code.pair tapeHeadCode tapeRightCode) _ _ _
    hpair (listCons_encoded t.head t.right)
  have hresult := evalPairSome _ _ _ _ _ hleft (evalPairSome _ _ _ _ _ hhead hright)
  have ht : moveLeft t = ⟨t.left.tail, t.left.head?.getD .blank, t.head :: t.right⟩ := by
    cases t with
    | mk left head right => cases left <;> rfl
  rw [ht, tape_encoded]
  exact hresult

theorem tapeMoveRightCode_eval (t : Tape) :
    tapeMoveRightCode.eval (Encodable.encode t) = Part.some (Encodable.encode (moveRight t)) := by
  have hpair := evalPairSome tapeHeadCode tapeLeftCode _ _ _
    (tapeHeadCode_eval t) (tapeLeftCode_eval t)
  have hleft := evalCompSome listConsCode (Code.pair tapeHeadCode tapeLeftCode) _ _ _
    hpair (listCons_encoded t.head t.left)
  have hhead := evalCompSome listHeadCode tapeRightCode _ _ _
    (tapeRightCode_eval t) (listHead_symbol t.right)
  have hright := evalCompSome listTailCode tapeRightCode _ _ _
    (tapeRightCode_eval t) (listTail_symbol t.right)
  have hresult := evalPairSome _ _ _ _ _ hleft (evalPairSome _ _ _ _ _ hhead hright)
  have ht : moveRight t = ⟨t.head :: t.left, t.right.head?.getD .blank, t.right.tail⟩ := by
    cases t with
    | mk left head right => cases right <;> rfl
  rw [ht, tape_encoded]
  exact hresult

theorem tapeWriteCode_eval (s : Symbol) (t : Tape) :
    tapeWriteCode.eval (Nat.pair (Encodable.encode s) (Encodable.encode t)) =
      Part.some (Encodable.encode { t with head := s }) := by
  let input := Nat.pair (Encodable.encode s) (Encodable.encode t)
  have hinRight : Code.eval .right input = Part.some (Encodable.encode t) := by
    simp [input, Code.eval]
  have hinLeft : Code.eval .left input = Part.some (Encodable.encode s) := by
    simp [input, Code.eval]
  have hleft := evalCompSome tapeLeftCode .right _ _ _ hinRight (tapeLeftCode_eval t)
  have hright := evalCompSome tapeRightCode .right _ _ _ hinRight (tapeRightCode_eval t)
  have hresult := evalPairSome _ _ _ _ _ hleft (evalPairSome _ _ _ _ _ hinLeft hright)
  rw [tape_encoded]
  exact hresult

#print axioms tapeMoveLeftCode
#print axioms tapeMoveRightCode
#print axioms tapeWriteCode
#print axioms tapeMoveLeftCode_eval
#print axioms tapeMoveRightCode_eval
#print axioms tapeWriteCode_eval
end LambdaTuring.Machine
