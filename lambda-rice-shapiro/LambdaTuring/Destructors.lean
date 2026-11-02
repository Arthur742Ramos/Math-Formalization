/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DecodeComputable
public meta import LambdaTuring.DecodeComputable

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

/-- The payload of an encoded abstraction, when the outer tag is abstraction. -/
def codeAbs (c : Code) : Option Code :=
  Code.recOn c none none none none
    (fun _ _ _ _ => none) (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun child _ => some child)

theorem primrec_codeAbs : Primrec codeAbs := by
  have hrf : Primrec₂ (fun (_ : Code) (p : Code × Option Code) => some p.1) :=
    Primrec.option_some.comp (Primrec.fst.comp Primrec.snd)
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => none)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ _ => none) (co := fun _ _ => none) (pc := fun _ _ => none)
    (rf := fun _ p => some p.1)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec₂.const _) (Primrec₂.const _) (Primrec₂.const _) hrf
  exact h.of_eq (fun _ => rfl)

/-- Destruct a lambda term only when it is an abstraction. -/
def termAbs? : Term → Option Term
  | .abs body => some body
  | _ => none

theorem termAbs_code (t : Term) :
    (codeAbs (encodeTerm t)).bind decodeTerm = termAbs? t := by
  cases t <;> simp [codeAbs, encodeTerm, termAbs?, decodeTerm_encodeTerm]

theorem primrec_termAbs : Primrec termAbs? := by
  have h := (Primrec.option_bind₁ primrec_decodeTerm).comp
    (primrec_codeAbs.comp primrec_encodeTerm)
  exact h.of_eq termAbs_code

/-- Extract a variable index only from a canonical variable tag. -/
def codeVar (c : Code) : Option Nat :=
  Code.recOn c none none none none
    (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then decodeConst g else none)
    (fun _ _ => none)

theorem primrec_codeVar : Primrec codeVar := by
  have hpc : Primrec₂ (fun (_ : Code) (p : Code × Code × Option Nat × Option Nat) =>
      if Encodable.encode p.1 = Encodable.encode Code.zero then decodeConst p.2.1 else none) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.const (Encodable.encode Code.zero))
    · exact primrec_decodeConst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    · exact Primrec.const none
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => none)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ _ => none) (co := fun _ _ => none)
    (pc := fun _ p => if Encodable.encode p.1 = Encodable.encode Code.zero then decodeConst p.2.1 else none)
    (rf := fun _ _ => none)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    (Primrec₂.const _) (Primrec₂.const _) hpc (Primrec₂.const _)
  exact h.of_eq (fun _ => rfl)

def termVar? : Term → Option Nat
  | .var i => some i
  | _ => none

theorem termVar_code (t : Term) : codeVar (encodeTerm t) = termVar? t := by
  cases t <;> simp [codeVar, encodeTerm, termVar?, decodeConst_const]

theorem primrec_termVar : Primrec termVar? :=
  (primrec_codeVar.comp primrec_encodeTerm).of_eq termVar_code


/-- Return the two immediate subcodes of an application. -/
def codeApp (c : Code) : Option (Code × Code) :=
  Code.recOn c none none none none
    (fun a b _ _ => some (a, b)) (fun _ _ _ _ => none) (fun _ _ _ _ => none)
    (fun _ _ => none)

theorem primrec_codeApp : Primrec codeApp := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × Option (Code × Code) × Option (Code × Code)) =>
      some (p.1, p.2.1)) :=
    Primrec.option_some.comp (Primrec.pair (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => none)
    (s := fun _ : Code => none) (l := fun _ : Code => none) (r := fun _ : Code => none)
    (pr := fun _ p => some (p.1, p.2.1)) (co := fun _ _ => none) (pc := fun _ _ => none)
    (rf := fun _ _ => none)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) (Primrec₂.const _) (Primrec₂.const _)
  exact h.of_eq (fun _ => rfl)

def decodeCodePair (p : Code × Code) : Option (Term × Term) := do
  let a ← decodeTerm p.1
  let b ← decodeTerm p.2
  pure (a, b)

theorem primrec_decodeCodePair : Primrec decodeCodePair := by
  unfold decodeCodePair
  apply Primrec.option_bind (primrec_decodeTerm.comp Primrec.fst)
  apply Primrec₂.mk
  refine (Primrec.option_map (primrec_decodeTerm.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).of_eq ?_
  intro p
  cases decodeTerm p.1.2 <;> simp

def termApp? : Term → Option (Term × Term)
  | .app a b => some (a, b)
  | _ => none

theorem termApp_code (t : Term) :
    (codeApp (encodeTerm t)).bind decodeCodePair = termApp? t := by
  cases t <;> simp [codeApp, encodeTerm, termApp?, decodeCodePair, decodeTerm_encodeTerm]

theorem primrec_termApp : Primrec termApp? := by
  have h := (Primrec.option_bind₁ primrec_decodeCodePair).comp
    (primrec_codeApp.comp primrec_encodeTerm)
  exact h.of_eq termApp_code

#print axioms primrec_termApp
#print axioms primrec_termAbs
#print axioms primrec_termVar

end LambdaTuring
