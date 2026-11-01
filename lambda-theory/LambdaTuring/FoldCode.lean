/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.TermCode
public meta import LambdaTuring.TermCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

def foldConst (c : Code) : Option Nat :=
  Code.recOn c (some 0) none none none
    (fun _ _ _ _ => none)
    (fun f _ _ rec => if Encodable.encode f = Encodable.encode Code.succ then rec.map Nat.succ else none)
    (fun _ _ _ _ => none)
    (fun _ _ => none)

theorem foldConst_eq_decodeConst (c : Code) : foldConst c = decodeConst c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair a b ia ib => rfl
  | prec a b ia ib => rfl
  | rfind' a ia => rfl
  | comp a b ia ib =>
    simp only [foldConst] at ib
    cases a <;> simp [foldConst, decodeConst, ib, Encodable.encode_injective.eq_iff]

theorem primrec_foldConst : Primrec foldConst := by
  have hco : Primrec₂ (fun (_ : Code) (p : Code × Code × Option Nat × Option Nat) =>
      if Encodable.encode p.1 = Encodable.encode Code.succ then p.2.2.2.map Nat.succ else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const (Encodable.encode Code.succ))
    · exact (Primrec.option_map₁ Primrec.succ).comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const none
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => some 0)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ _ => none)
    (co := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.succ then p.2.2.2.map Nat.succ else none)
    (pc := fun _ _ => none) (rf := fun _ _ => none)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec₂.const _) hco (Primrec₂.const _) (Primrec₂.const _)
  exact h.of_eq (fun c => by rfl)

theorem primrec_decodeConst : Primrec decodeConst :=
  primrec_foldConst.of_eq foldConst_eq_decodeConst


/-- Decide whether a recursive-code tree is a canonical encoded lambda term. -/
def validCode (c : Code) : Bool :=
  Code.recOn c false false false false
    (fun _ _ ra rb => ra && rb)
    (fun _ _ _ _ => false)
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then (decodeConst g).isSome else false)
    (fun _ rec => rec)

theorem primrec_validCode : Primrec validCode := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × Bool × Bool) => p.2.2.1 && p.2.2.2) := by
    exact Primrec.and.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hpc : Primrec₂ (fun (_ : Code) (p : Code × Code × Bool × Bool) =>
      if Encodable.encode p.1 = Encodable.encode Code.zero then (decodeConst p.2.1).isSome else false) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const (Encodable.encode Code.zero))
    · exact Primrec.option_isSome.comp (primrec_decodeConst.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const false
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => false)
    (s := fun _ : Code => false) (l := fun _ : Code => false) (r := fun _ : Code => false)
    (pr := fun _ p => p.2.2.1 && p.2.2.2)
    (co := fun _ _ => false)
    (pc := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.zero then (decodeConst p.2.1).isSome else false)
    (rf := fun _ p => p.2)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc (Primrec₂.mk (Primrec.snd.comp Primrec.snd))
  exact h.of_eq (fun c => by rfl)

theorem validCode_decodeTerm (c : Code) : validCode c = (decodeTerm c).isSome := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | comp a b ia ib => rfl
  | pair a b ia ib =>
    change (validCode a && validCode b) = (decodeTerm (Code.pair a b)).isSome
    cases ha : decodeTerm a <;> cases hb : decodeTerm b <;>
      simp [decodeTerm, ia, ib, ha, hb]
  | rfind' a ia =>
    change validCode a = ((decodeTerm a).map Term.abs).isSome
    cases ha : decodeTerm a <;> simp [ia, ha]
  | prec a b ia ib =>
    cases a <;> simp [validCode, decodeTerm, Encodable.encode_injective.eq_iff]

theorem validCode_iff (c : Code) : validCode c = true ↔ ∃ t, c = encodeTerm t := by
  rw [validCode_decodeTerm, Option.isSome_iff_exists]
  simp only [decodeTerm_eq_some_iff]


theorem validCode_primrecPred : PrimrecPred (fun c => validCode c = true) := by
  apply Primrec.primrecPred
  convert primrec_validCode using 1
  funext c
  cases validCode c <;> simp

abbrev ValidCode := { c : Code // validCode c = true }

instance : Primcodable ValidCode := Primcodable.subtype validCode_primrecPred

/-- Term syntax is equivalent to the primitive-recursively recognized code image. -/
noncomputable def termEquivValid : Term ≃ ValidCode where
  toFun t := ⟨encodeTerm t, (validCode_iff _).2 ⟨t, rfl⟩⟩
  invFun c := Classical.choose ((validCode_iff c.val).1 c.property)
  left_inv t := by
    apply encodeTerm_injective
    exact (Classical.choose_spec ((validCode_iff (encodeTerm t)).1
      ((validCode_iff (encodeTerm t)).2 ⟨t, rfl⟩))).symm
  right_inv c := by
    apply Subtype.ext
    exact (Classical.choose_spec ((validCode_iff c.val).1 c.property)).symm

/-- Effective coding for terms, induced by the explicit canonical code image. -/
noncomputable instance : Primcodable Term := Primcodable.ofEquiv ValidCode termEquivValid

theorem primrec_encodeTerm : Primrec encodeTerm := by
  have h : Primrec termEquivValid := Primrec.of_equiv
  have hv : Primrec (@Subtype.val Code (fun c => validCode c = true)) :=
    Primrec.subtype_val (hp := validCode_primrecPred)
  exact (hv.comp h).of_eq (fun t => rfl)


theorem primrec_var : Primrec Term.var := by
  apply (Primrec.of_equiv_iff termEquivValid).1
  apply (Primrec.subtype_val_iff (hp := validCode_primrecPred)).1
  change Primrec (fun n : Nat => Code.prec Code.zero (Code.const n))
  exact Code.primrec₂_prec.comp (Primrec.const Code.zero) primrec_constCode

theorem primrec_abs : Primrec Term.abs := by
  apply (Primrec.of_equiv_iff termEquivValid).1
  apply (Primrec.subtype_val_iff (hp := validCode_primrecPred)).1
  change Primrec (fun t : Term => Code.rfind' (encodeTerm t))
  exact Code.primrec_rfind'.comp primrec_encodeTerm

theorem primrec_app : Primrec₂ Term.app := by
  apply (Primrec.of_equiv_iff termEquivValid).1
  apply (Primrec.subtype_val_iff (hp := validCode_primrecPred)).1
  change Primrec (fun p : Term × Term => Code.pair (encodeTerm p.1) (encodeTerm p.2))
  exact Code.primrec₂_pair.comp (primrec_encodeTerm.comp Primrec.fst) (primrec_encodeTerm.comp Primrec.snd)

#print axioms primrec_var
#print axioms primrec_abs
#print axioms primrec_app
#print axioms primrec_encodeTerm
#print axioms primrec_validCode
#print axioms validCode_iff
#print axioms primrec_decodeConst

end LambdaTuring
