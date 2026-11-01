/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.StandardReduction
public meta import LambdaTuring.StandardReduction
public import LambdaTuring.CPSProjection
public meta import LambdaTuring.CPSProjection

@[expose] public section

open Nat.Partrec

namespace LambdaTuring

/-- A total structural compiler for Mathlib's partial-recursive code syntax. -/
def compileCPSTotal : Nat.Partrec.Code → Term
  | .zero => cpsConstant 0
  | .succ => cpsSuccessor
  | .left => cpsLiftTotal churchNumericLeft
  | .right => cpsLiftTotal churchNumericRight
  | .pair f g => cpsPair (compileCPSTotal f) (compileCPSTotal g)
  | .comp f g => cpsCompose (compileCPSTotal f) (compileCPSTotal g)
  | .prec f g => cpsRecursion (compileCPSTotal f) (compileCPSTotal g)
  | .rfind' f => cpsMinimize (compileCPSTotal f)

theorem compileCPSTotal_sound (c : Nat.Partrec.Code) :
    CPSRepresents (compileCPSTotal c) (Nat.Partrec.Code.eval c) := by
  induction c with
  | zero => simpa [compileCPSTotal, Nat.Partrec.Code.const] using cpsConstant_represents 0
  | succ => exact cpsSuccessor_represents
  | left => exact cpsNumericLeft_represents
  | right => exact cpsNumericRight_represents
  | pair f g ihf ihg =>
    rw [codePair_eval]
    exact cpsPair_represents ihf ihg
  | comp f g ihf ihg =>
    have heval : Nat.Partrec.Code.eval (.comp f g) =
        (fun n => (Nat.Partrec.Code.eval g n).bind (Nat.Partrec.Code.eval f)) := by
      funext n
      exact Part.bind_eq_bind _ _
    rw [heval]
    exact cpsCompose_represents ihf ihg
  | prec f g ihf ihg => exact cpsRecursion_code ihf ihg
  | rfind' f ih => exact cpsMinimize_code ih

/-- The exported unary lambda program has the exact partial numerical result. -/
def compileLambdaTotal (c : Nat.Partrec.Code) : Term := cpsUnary (compileCPSTotal c)

theorem compileLambdaTotal_sound (c : Nat.Partrec.Code) :
    Represents (compileLambdaTotal c) (Nat.Partrec.Code.eval c) :=
  cpsUnary_represents (compileCPSTotal_sound c)

def compileCPSTotalFold (c : Nat.Partrec.Code) : Term :=
  Nat.Partrec.Code.recOn c (cpsConstant 0) cpsSuccessor
    (cpsLiftTotal churchNumericLeft) (cpsLiftTotal churchNumericRight)
    (fun _ _ F G => cpsPair F G) (fun _ _ F G => cpsCompose F G)
    (fun _ _ F G => cpsRecursion F G) (fun _ F => cpsMinimize F)

theorem compileCPSTotalFold_eq (c : Nat.Partrec.Code) : compileCPSTotalFold c = compileCPSTotal c := by
  induction c with
  | zero | succ | left | right => rfl
  | pair f g ihf ihg => simpa [compileCPSTotalFold, compileCPSTotal] using congrArg₂ cpsPair ihf ihg
  | comp f g ihf ihg => simpa [compileCPSTotalFold, compileCPSTotal] using congrArg₂ cpsCompose ihf ihg
  | prec f g ihf ihg => simpa [compileCPSTotalFold, compileCPSTotal] using congrArg₂ cpsRecursion ihf ihg
  | rfind' f ih => simpa [compileCPSTotalFold, compileCPSTotal] using congrArg cpsMinimize ih

set_option maxHeartbeats 1000000 in
theorem primrec_compileCPSTotalFold : Primrec compileCPSTotalFold := by
  let A := Nat.Partrec.Code
  let P := A × A × Term × Term
  let S := A × P
  have hl : Primrec (fun s : S => s.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun s : S => s.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hpr : Primrec₂ (fun (_ : A) (p : P) => cpsPair p.2.2.1 p.2.2.2) := primrec_cpsPair.comp hl hr
  have hco : Primrec₂ (fun (_ : A) (p : P) => cpsCompose p.2.2.1 p.2.2.2) := primrec_cpsCompose.comp hl hr
  have hpc : Primrec₂ (fun (_ : A) (p : P) => cpsRecursion p.2.2.1 p.2.2.2) := primrec_cpsRecursion.comp hl hr
  have hrf : Primrec₂ (fun (_ : A) (p : A × Term) => cpsMinimize p.2) :=
    primrec_cpsMinimize.comp (Primrec.snd.comp Primrec.snd)
  have h := Nat.Partrec.Code.primrec_recOn'
    (c := id) (z := fun _ : A => cpsConstant 0)
    (s := fun _ : A => cpsSuccessor) (l := fun _ : A => cpsLiftTotal churchNumericLeft)
    (r := fun _ : A => cpsLiftTotal churchNumericRight)
    (pr := fun _ p => cpsPair p.2.2.1 p.2.2.2)
    (co := fun _ p => cpsCompose p.2.2.1 p.2.2.2)
    (pc := fun _ p => cpsRecursion p.2.2.1 p.2.2.2)
    (rf := fun _ p => cpsMinimize p.2)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr hco hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_compileCPSTotal : Primrec compileCPSTotal :=
  primrec_compileCPSTotalFold.of_eq compileCPSTotalFold_eq

theorem primrec_compileLambdaTotal : Primrec compileLambdaTotal :=
  primrec_cpsUnary.comp primrec_compileCPSTotal

#print axioms compileCPSTotal_sound
#print axioms compileLambdaTotal_sound
#print axioms primrec_compileLambdaTotal

end LambdaTuring
