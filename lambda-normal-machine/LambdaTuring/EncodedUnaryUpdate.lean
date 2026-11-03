/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EncodedSubCode
public meta import LambdaTuring.EncodedSubCode

@[expose] public section

namespace LambdaTuring.Machine
open Nat.Partrec
open LambdaTuring.EffectiveCode

/-- A padding observation leaves the accumulator untouched; a present symbol
    updates the encoded optional unary count. -/
def unaryItemCode : Code := .left
def unaryAccCode : Code := .right
def unaryPredItemCode : Code := .comp predCode unaryItemCode
def unaryPred2ItemCode : Code := .comp predCode unaryPredItemCode
def unaryPredAccCode : Code := .comp predCode unaryAccCode
def unarySuccAccCode : Code := .comp .succ unaryAccCode
def unaryBlankCode : Code :=
  chooseZeroCode unaryAccCode .zero (chooseZeroCode unaryPredAccCode (Code.const 1) .zero)
def unaryOneCode : Code := chooseZeroCode unaryAccCode .zero unarySuccAccCode
def unaryUpdateCode : Code :=
  chooseZeroCode unaryItemCode unaryAccCode
    (chooseZeroCode unaryPredItemCode unaryBlankCode
      (chooseZeroCode unaryPred2ItemCode unaryOneCode .zero))

theorem unaryUpdateCode_eval (item acc : Nat) :
    unaryUpdateCode.eval (Nat.pair item acc) = Part.some
      (if item = 0 then acc else
        if item.pred = 0 then
          (if acc = 0 then 0 else if acc.pred = 0 then 1 else 0)
        else if item.pred.pred = 0 then (if acc = 0 then 0 else acc + 1) else 0) := by
  let input := Nat.pair item acc
  have hi : unaryItemCode.eval input = Part.some item := by simp [input, unaryItemCode, Code.eval]
  have ha : unaryAccCode.eval input = Part.some acc := by simp [input, unaryAccCode, Code.eval]
  have hz : Code.eval .zero input = Part.some 0 := rfl
  have hone : (Code.const 1).eval input = Part.some 1 := Code.eval_const 1 input
  have hpi := evalCompSome predCode unaryItemCode _ _ _ hi (eval_predCode item)
  have hp2i := evalCompSome predCode unaryPredItemCode _ _ _ hpi (eval_predCode item.pred)
  have hpa := evalCompSome predCode unaryAccCode _ _ _ ha (eval_predCode acc)
  have hsa := evalCompSome .succ unaryAccCode _ _ _ ha (show Code.eval .succ acc = Part.some (acc + 1) from rfl)
  have hblankInner := chooseZeroCode_eval unaryPredAccCode (Code.const 1) .zero _ _ _ _ hpa hone hz
  have hblank := chooseZeroCode_eval unaryAccCode .zero
    (chooseZeroCode unaryPredAccCode (Code.const 1) .zero) _ _ _ _ ha hz hblankInner
  have honeResult := chooseZeroCode_eval unaryAccCode .zero unarySuccAccCode _ _ _ _ ha hz hsa
  have hnotBlank := chooseZeroCode_eval unaryPred2ItemCode unaryOneCode .zero _ _ _ _ hp2i honeResult hz
  have hnotEmpty := chooseZeroCode_eval unaryPredItemCode unaryBlankCode
    (chooseZeroCode unaryPred2ItemCode unaryOneCode .zero) _ _ _ _ hpi hblank hnotBlank
  have hresult := chooseZeroCode_eval unaryItemCode unaryAccCode
    (chooseZeroCode unaryPredItemCode unaryBlankCode
      (chooseZeroCode unaryPred2ItemCode unaryOneCode .zero)) _ _ _ _ hi ha hnotEmpty
  exact hresult

theorem unaryCount_zero_iff (xs : List Symbol) :
    unaryCount xs = some 0 ↔ blanksOnly xs = true := by
  induction xs with
  | nil => simp [unaryCount, blanksOnly]
  | cons s xs ih =>
    cases s with
    | blank =>
      cases h : blanksOnly xs <;> simp [unaryCount, blanksOnly, h]
    | one =>
      cases h : unaryCount xs with
      | none => simp [unaryCount, blanksOnly, h]
      | some n => cases n <;> simp [unaryCount, blanksOnly, h]
    | mark => simp [unaryCount, blanksOnly]

theorem unaryUpdateCode_symbol (s : Symbol) (xs : List Symbol) :
    unaryUpdateCode.eval (Nat.pair (Encodable.encode (some s)) (Encodable.encode (unaryCount xs))) =
      Part.some (Encodable.encode (unaryCount (s :: xs))) := by
  rw [unaryUpdateCode_eval]
  cases s with
  | blank =>
    cases hc : unaryCount xs with
    | none =>
      have hb : blanksOnly xs = false := by
        cases h : blanksOnly xs with
        | false => rfl
        | true => have := (unaryCount_zero_iff xs).2 h; simp [hc] at this
      simp [unaryCount, hb, symbol_encoded, symbolIndex]
    | some n =>
      cases n with
      | zero =>
        have hb : blanksOnly xs = true := (unaryCount_zero_iff xs).1 hc
        simp [unaryCount, hb, symbol_encoded, symbolIndex]
      | succ n =>
        have hb : blanksOnly xs = false := by
          cases h : blanksOnly xs with
          | false => rfl
          | true => have := (unaryCount_zero_iff xs).2 h; simp [hc] at this
        simp [unaryCount, hb, symbol_encoded, symbolIndex]
  | one =>
    cases hc : unaryCount xs with
    | none => simp [unaryCount, hc, symbol_encoded, symbolIndex]
    | some n => simp [unaryCount, hc, symbol_encoded, symbolIndex]
  | mark =>
    simp [unaryCount, symbol_encoded, symbolIndex]

theorem unaryUpdateCode_padding (xs : List Symbol) :
    unaryUpdateCode.eval (Nat.pair (Encodable.encode (none : Option Symbol))
      (Encodable.encode (unaryCount xs))) = Part.some (Encodable.encode (unaryCount xs)) := by
  simp [unaryUpdateCode_eval]

theorem unaryUpdateCode_optional (item : Option Symbol) (xs : List Symbol) :
    unaryUpdateCode.eval (Nat.pair (Encodable.encode item) (Encodable.encode (unaryCount xs))) =
      Part.some (Encodable.encode (unaryCount (item.toList ++ xs))) := by
  cases item with
  | none => simpa using unaryUpdateCode_padding xs
  | some s => simpa using unaryUpdateCode_symbol s xs

#print axioms unaryUpdateCode
#print axioms unaryUpdateCode_eval
#print axioms unaryUpdateCode_symbol
end LambdaTuring.Machine
