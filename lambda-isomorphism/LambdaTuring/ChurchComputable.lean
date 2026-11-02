/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Destructors
public meta import LambdaTuring.Destructors
public import LambdaTuring.ObservationSearch
public meta import LambdaTuring.ObservationSearch

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

theorem primrec_churchBody : Primrec churchBody := by
  have step : Primrec₂ (fun (_ : Nat) (t : Term) => Term.app (.var 1) t) :=
    primrec_app.comp₂ (Primrec₂.const _) Primrec₂.right
  have h := Primrec.nat_rec₁ (.var 0) step
  convert h using 1
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp [churchBody, ih]

theorem primrec_church : Primrec church := by
  change Primrec (fun n => Term.abs (Term.abs (churchBody n)))
  exact primrec_abs.comp (primrec_abs.comp primrec_churchBody)

/-- A code fold recognizing the body of a Church numeral. -/
def foldChurchBody (c : Code) : Option Nat :=
  Code.recOn c none none none none
    (fun f _ _ rec => if Encodable.encode f = Encodable.encode (encodeTerm (.var 1)) then
      rec.map Nat.succ else none)
    (fun _ _ _ _ => none)
    (fun f g _ _ => if Encodable.encode (Code.prec f g) = Encodable.encode (encodeTerm (.var 0)) then
      some 0 else none)
    (fun _ _ => none)

theorem primrec_foldChurchBody : Primrec foldChurchBody := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × Option Nat × Option Nat) =>
      if Encodable.encode p.1 = Encodable.encode (encodeTerm (.var 1)) then
        p.2.2.2.map Nat.succ else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const (Encodable.encode (encodeTerm (.var 1))))
    · exact (Primrec.option_map₁ Primrec.succ).comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const none
  have hpc : Primrec₂ (fun (_ : Code) (p : Code × Code × Option Nat × Option Nat) =>
      if Encodable.encode (Code.prec p.1 p.2.1) = Encodable.encode (encodeTerm (.var 0)) then
        some 0 else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Code.primrec₂_prec.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const (Encodable.encode (encodeTerm (.var 0))))
    · exact Primrec.const _
    · exact Primrec.const _
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => none)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ p => if Encodable.encode p.1 = Encodable.encode (encodeTerm (.var 1)) then
      p.2.2.2.map Nat.succ else none)
    (co := fun _ _ => none)
    (pc := fun _ p => if Encodable.encode (Code.prec p.1 p.2.1) = Encodable.encode (encodeTerm (.var 0)) then
      some 0 else none)
    (rf := fun _ _ => none)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc (Primrec₂.const _)
  exact h.of_eq (fun _ => rfl)

theorem foldChurchBody_encode (t : Term) : foldChurchBody (encodeTerm t) = decodeChurchBody t := by
  induction t with
  | var n =>
    change (if Encodable.encode (encodeTerm (.var n)) = Encodable.encode (encodeTerm (.var 0)) then
      some 0 else none) = decodeChurchBody (.var n)
    simp only [Encodable.encode_injective.eq_iff, encodeTerm_injective.eq_iff]
    cases n <;> simp [decodeChurchBody]
  | abs t ih => rfl
  | app f x ihf ihx =>
    change (if Encodable.encode (encodeTerm f) = Encodable.encode (encodeTerm (.var 1)) then
      (foldChurchBody (encodeTerm x)).map Nat.succ else none) = decodeChurchBody (.app f x)
    rw [ihx]
    simp only [Encodable.encode_injective.eq_iff, encodeTerm_injective.eq_iff]
    cases f with
    | var n => cases n with
      | zero => simp [decodeChurchBody]
      | succ n => cases n <;> simp [decodeChurchBody]
    | abs f => simp [decodeChurchBody]
    | app a b => simp [decodeChurchBody]

theorem primrec_decodeChurchBody : Primrec decodeChurchBody :=
  (primrec_foldChurchBody.comp primrec_encodeTerm).of_eq foldChurchBody_encode


theorem primrec_decodeChurch : Primrec decodeChurch := by
  have inner : Primrec (fun t => (termAbs? t).bind decodeChurchBody) :=
    (Primrec.option_bind₁ primrec_decodeChurchBody).comp primrec_termAbs
  have h : Primrec (fun t => (termAbs? t).bind (fun a => (termAbs? a).bind decodeChurchBody)) :=
    (Primrec.option_bind₁ inner).comp primrec_termAbs
  apply h.of_eq
  intro t
  cases t with
  | var i => rfl
  | app f x => rfl
  | abs t => cases t <;> rfl

#print axioms primrec_decodeChurch
#print axioms primrec_church
#print axioms primrec_decodeChurchBody

end LambdaTuring
