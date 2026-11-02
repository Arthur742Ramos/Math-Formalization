/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.FoldCode
public meta import LambdaTuring.FoldCode

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

def foldTerm (c : Code) : Option Term :=
  Code.recOn c none none none none
    (fun _ _ ra rb => ra.bind fun a => rb.map (Term.app a))
    (fun _ _ _ _ => none)
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then
      (decodeConst g).map Term.var else none)
    (fun _ rec => rec.map Term.abs)

theorem foldTerm_eq_decodeTerm (c : Code) : foldTerm c = decodeTerm c := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | comp a b ia ib => rfl
  | pair a b ia ib =>
    change (foldTerm a).bind (fun x => (foldTerm b).map (Term.app x)) = decodeTerm (Code.pair a b)
    rw [ia, ib]
    cases ha : decodeTerm a <;> cases hb : decodeTerm b <;> simp [decodeTerm, ha, hb]
  | rfind' a ia =>
    change (foldTerm a).map Term.abs = decodeTerm (Code.rfind' a)
    rw [ia]
    rfl
  | prec a b ia ib =>
    cases a <;> simp [foldTerm, decodeTerm, Encodable.encode_injective.eq_iff]

theorem primrec_foldTerm : Primrec foldTerm := by
  let P := Code × Code × Option Term × Option Term
  have oa : Primrec (fun x : Code × P => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ob : Primrec (fun x : Code × P => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hpr : Primrec₂ (fun (_ : Code) (p : P) =>
      p.2.2.1.bind fun a => p.2.2.2.map (Term.app a)) := by
    apply Primrec.option_bind oa
    apply Primrec₂.mk
    apply Primrec.option_map (ob.comp Primrec.fst)
    exact (primrec_app.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hpc : Primrec₂ (fun (_ : Code) (p : P) =>
      if Encodable.encode p.1 = Encodable.encode Code.zero then
        (decodeConst p.2.1).map Term.var else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const (Encodable.encode Code.zero))
    · exact (Primrec.option_map₁ primrec_var).comp (primrec_decodeConst.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    · exact Primrec.const none
  have hrf : Primrec₂ (fun (_ : Code) (p : Code × Option Term) => p.2.map Term.abs) := by
    exact (Primrec.option_map₁ primrec_abs).comp (Primrec.snd.comp Primrec.snd)
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => none)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ p => p.2.2.1.bind fun a => p.2.2.2.map (Term.app a))
    (co := fun _ _ => none)
    (pc := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.zero then
      (decodeConst p.2.1).map Term.var else none)
    (rf := fun _ p => p.2.map Term.abs)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc hrf
  exact h.of_eq (fun c => by rfl)

theorem primrec_decodeTerm : Primrec decodeTerm :=
  primrec_foldTerm.of_eq foldTerm_eq_decodeTerm

#print axioms primrec_decodeTerm

end LambdaTuring
