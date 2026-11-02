/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.BetaStepComputable
public meta import LambdaTuring.BetaStepComputable

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

def termSize : Term → Nat
  | .var _ => 1
  | .abs t => termSize t + 1
  | .app a b => termSize a + termSize b + 1

/-- Fold size across the canonical code tree; other code tags default to zero. -/
def codeTermSize (c : Code) : Nat :=
  Code.recOn c 0 0 0 0
    (fun _ _ a b => a + b + 1)
    (fun _ _ _ _ => 0)
    (fun _ _ _ _ => 1)
    (fun _ a => a + 1)

theorem codeTermSize_encode (t : Term) : codeTermSize (encodeTerm t) = termSize t := by
  induction t with
  | var n => rfl
  | abs t ih => change codeTermSize (encodeTerm t) + 1 = termSize t + 1; rw [ih]
  | app a b ia ib =>
    change codeTermSize (encodeTerm a) + codeTermSize (encodeTerm b) + 1 = termSize a + termSize b + 1
    rw [ia, ib]

theorem primrec_codeTermSize : Primrec codeTermSize := by
  have hpr : Primrec₂ (fun (_ : Code) (p : Code × Code × Nat × Nat) => p.2.2.1 + p.2.2.2 + 1) :=
    Primrec.succ.comp (Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hrf : Primrec₂ (fun (_ : Code) (p : Code × Nat) => p.2 + 1) :=
    Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  have h := Code.primrec_recOn'
    (c := id) (z := fun _ : Code => 0)
    (s := fun _ : Code => 0) (l := fun _ : Code => 0) (r := fun _ : Code => 0)
    (pr := fun _ p => p.2.2.1 + p.2.2.2 + 1)
    (co := fun _ _ => 0) (pc := fun _ _ => 1) (rf := fun _ p => p.2 + 1)
    Primrec.id (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) (Primrec₂.const _) hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_termSize : Primrec termSize :=
  (primrec_codeTermSize.comp primrec_encodeTerm).of_eq codeTermSize_encode

theorem termSize_pos (t : Term) : 0 < termSize t := by
  cases t <;> simp [termSize]

#print axioms primrec_termSize

end LambdaTuring
