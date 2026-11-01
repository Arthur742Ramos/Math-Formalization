/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Basic
public meta import LambdaTuring.Basic
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-! A concrete injection of lambda syntax into Mathlib partial-recursive code.
This does not yet prove that the encoded beta operations are partial recursive. -/

namespace LambdaTuring

open Nat.Partrec

def encodeTerm (t : Term) : Code :=
  Term.rec (fun n => .prec .zero (Code.const n))
    (fun _ r => .rfind' r)
    (fun _ _ ra rb => .pair ra rb) t

def decodeConst : Code → Option Nat
  | .zero => some 0
  | .comp .succ c => (decodeConst c).map Nat.succ
  | _ => none

def decodeTerm : Code → Option Term
  | .prec .zero c => (decodeConst c).map Term.var
  | .rfind' c => (decodeTerm c).map Term.abs
  | .pair a b => do
      let a' ← decodeTerm a
      let b' ← decodeTerm b
      pure (.app a' b')
  | _ => none

theorem decodeConst_const (n : Nat) : decodeConst (Code.const n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Code.const, decodeConst, ih]


theorem decodeConst_sound (c : Code) (n : Nat) :
    decodeConst c = some n → c = Code.const n := by
  induction c generalizing n with
  | zero =>
    intro h
    have : n = 0 := by simpa [decodeConst] using h.symm
    subst n
    rfl
  | succ => simp [decodeConst]
  | left => simp [decodeConst]
  | right => simp [decodeConst]
  | pair a b ia ib => simp [decodeConst]
  | prec a b ia ib => simp [decodeConst]
  | rfind' a ia => simp [decodeConst]
  | comp a b ia ib =>
    cases a with
    | zero => simp [decodeConst]
    | succ =>
      change (decodeConst b).map Nat.succ = some n → Code.comp Code.succ b = Code.const n
      rw [Option.map_eq_some_iff]
      rintro ⟨k, hk, rfl⟩
      simpa [Code.const] using congrArg (Code.comp Code.succ) (ib k hk)
    | left => simp [decodeConst]
    | right => simp [decodeConst]
    | pair x y => simp [decodeConst]
    | comp x y => simp [decodeConst]
    | prec x y => simp [decodeConst]
    | rfind' x => simp [decodeConst]

theorem decodeTerm_encodeTerm (t : Term) : decodeTerm (encodeTerm t) = some t := by
  induction t with
  | var n => simp [encodeTerm, decodeTerm, decodeConst_const]
  | abs t ih => simp [encodeTerm, decodeTerm, ih]
  | app a b ia ib => simp [encodeTerm, decodeTerm, ia, ib]


theorem decodeTerm_sound (c : Code) (t : Term) :
    decodeTerm c = some t → c = encodeTerm t := by
  induction c generalizing t with
  | zero => simp [decodeTerm]
  | succ => simp [decodeTerm]
  | left => simp [decodeTerm]
  | right => simp [decodeTerm]
  | comp a b ia ib => simp [decodeTerm]
  | prec a b ia ib =>
    cases a with
    | zero =>
      change (decodeConst b).map Term.var = some t → Code.prec Code.zero b = encodeTerm t
      rw [Option.map_eq_some_iff]
      rintro ⟨n, hn, rfl⟩
      simp [encodeTerm, decodeConst_sound b n hn]
    | succ => simp [decodeTerm]
    | left => simp [decodeTerm]
    | right => simp [decodeTerm]
    | pair x y => simp [decodeTerm]
    | comp x y => simp [decodeTerm]
    | prec x y => simp [decodeTerm]
    | rfind' x => simp [decodeTerm]
  | rfind' a ia =>
    change (decodeTerm a).map Term.abs = some t → Code.rfind' a = encodeTerm t
    rw [Option.map_eq_some_iff]
    rintro ⟨u, hu, rfl⟩
    simp [encodeTerm, ia u hu]
  | pair a b ia ib =>
    cases ha : decodeTerm a with
    | none => simp [decodeTerm, ha]
    | some x =>
      cases hb : decodeTerm b with
      | none => simp [decodeTerm, ha, hb]
      | some y =>
        intro h
        have he : Term.app x y = t := by simpa [decodeTerm, ha, hb] using h
        subst t
        simp [encodeTerm, ia x ha, ib y hb]

theorem decodeTerm_eq_some_iff (c : Code) (t : Term) :
    decodeTerm c = some t ↔ c = encodeTerm t := by
  constructor
  · exact decodeTerm_sound c t
  · rintro rfl
    exact decodeTerm_encodeTerm t

theorem encodeTerm_injective : Function.Injective encodeTerm := by
  intro a b h
  have h' := congrArg decodeTerm h
  simpa only [decodeTerm_encodeTerm, Option.some.injEq] using h'


/-- Codes for numeric constants form a primitive-recursive sequence. -/
theorem primrec_constCode : Primrec Code.const := by
  have step : Primrec₂ (fun (_ : Nat) (c : Code) => Code.comp Code.succ c) :=
    Code.primrec₂_comp.comp₂ (Primrec₂.const Code.succ) Primrec₂.right
  have h := Primrec.nat_rec₁ Code.zero step
  convert h using 1
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp [Code.const, ih]

/-- The code of a Church body is primitive recursive in its index. -/
theorem primrec_churchBodyCode : Primrec (fun n => encodeTerm (churchBody n)) := by
  have step : Primrec₂ (fun (_ : Nat) (c : Code) => Code.pair (encodeTerm (.var 1)) c) :=
    Code.primrec₂_pair.comp₂ (Primrec₂.const _) Primrec₂.right
  have h := Primrec.nat_rec₁ (encodeTerm (.var 0)) step
  convert h using 1
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, encodeTerm, ih]

/-- Church numeral codes are produced by a primitive-recursive function. -/
theorem primrec_churchCode : Primrec (fun n => encodeTerm (church n)) := by
  simpa [church, encodeTerm] using
    Code.primrec_rfind'.comp (Code.primrec_rfind'.comp primrec_churchBodyCode)

#print axioms primrec_constCode
#print axioms primrec_churchCode
#print axioms decodeTerm_encodeTerm
#print axioms encodeTerm_injective

end LambdaTuring
