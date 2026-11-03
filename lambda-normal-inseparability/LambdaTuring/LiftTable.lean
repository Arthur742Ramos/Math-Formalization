/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.TermSize
public meta import LambdaTuring.TermSize

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

def tableAt (xs : List Term) (i : Nat) : Term := (xs[i]?).getD (.var 0)

def varLiftTable (bound n : Nat) : List Term :=
  (List.range (bound + 1)).map fun cutoff => .var (if n < cutoff then n else n + 1)

def absLiftTable (bound : Nat) (body : List Term) : List Term :=
  (List.range (bound + 1)).map fun cutoff => .abs (tableAt body (cutoff + 1))

def appLiftTable (bound : Nat) (f x : List Term) : List Term :=
  (List.range (bound + 1)).map fun cutoff => .app (tableAt f cutoff) (tableAt x cutoff)

/-- A bounded table of cutoff-sensitive shifts, built by a structural fold on codes. -/
def foldLift (bound : Nat) (c : Code) : List Term :=
  Code.recOn c [] [] [] []
    (fun _ _ a b => appLiftTable bound a b)
    (fun _ _ _ _ => [])
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then
      ((decodeConst g).map (varLiftTable bound)).getD [] else [])
    (fun _ body => absLiftTable bound body)

theorem tableAt_range_map (bound i : Nat) (f : Nat → Term) (h : i ≤ bound) :
    tableAt ((List.range (bound + 1)).map f) i = f i := by
  have hi : i < ((List.range (bound + 1)).map f).length := by simp; omega
  simp [tableAt, List.getElem?_eq_getElem hi]

theorem tableAt_varLiftTable (bound n i : Nat) (h : i ≤ bound) :
    tableAt (varLiftTable bound n) i = .var (if n < i then n else n + 1) :=
  tableAt_range_map bound i _ h

theorem tableAt_absLiftTable (bound i : Nat) (body : List Term) (h : i ≤ bound) :
    tableAt (absLiftTable bound body) i = .abs (tableAt body (i + 1)) :=
  tableAt_range_map bound i _ h

theorem tableAt_appLiftTable (bound i : Nat) (f x : List Term) (h : i ≤ bound) :
    tableAt (appLiftTable bound f x) i = .app (tableAt f i) (tableAt x i) :=
  tableAt_range_map bound i _ h

/-- The table is correct whenever enough unused cutoff entries remain. -/
theorem foldLift_correct (t : Term) (bound cutoff : Nat)
    (h : cutoff + termSize t ≤ bound) :
    tableAt (foldLift bound (encodeTerm t)) cutoff = liftFrom cutoff t := by
  induction t generalizing cutoff with
  | var n =>
    have hi : cutoff ≤ bound := by simp [termSize] at h; omega
    change tableAt (if Encodable.encode Code.zero = Encodable.encode Code.zero then
      ((decodeConst (Code.const n)).map (varLiftTable bound)).getD [] else []) cutoff = _
    simp only [ite_true, decodeConst_const, Option.map_some, Option.getD_some]
    exact tableAt_varLiftTable bound n cutoff hi
  | abs t ih =>
    have hi : cutoff ≤ bound := by simp [termSize] at h; omega
    have hc : cutoff + 1 + termSize t ≤ bound := by simp [termSize] at h; omega
    change tableAt (absLiftTable bound (foldLift bound (encodeTerm t))) cutoff = _
    rw [tableAt_absLiftTable bound cutoff _ hi, ih (cutoff + 1) hc]
    rfl
  | app f x ihf ihx =>
    have hi : cutoff ≤ bound := by simp [termSize] at h; omega
    have hf : cutoff + termSize f ≤ bound := by simp [termSize] at h; omega
    have hx : cutoff + termSize x ≤ bound := by simp [termSize] at h; omega
    change tableAt (appLiftTable bound (foldLift bound (encodeTerm f)) (foldLift bound (encodeTerm x))) cutoff = _
    rw [tableAt_appLiftTable bound cutoff _ _ hi, ihf cutoff hf, ihx cutoff hx]
    rfl


theorem primrec_tableAt : Primrec₂ tableAt :=
  Primrec.option_getD.comp₂ Primrec.list_getElem? (Primrec₂.const (Term.var 0))

theorem primrec_varLiftTable : Primrec₂ varLiftTable := by
  have hc : Primrec (fun p : (Nat × Nat) × Nat =>
      if p.1.2 < p.2 then p.1.2 else p.1.2 + 1) := by
    apply Primrec.ite
    · exact Primrec.nat_lt.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    · exact Primrec.snd.comp Primrec.fst
    · exact Primrec.succ.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    (primrec_var.comp hc).to₂

theorem primrec_absLiftTable : Primrec₂ absLiftTable := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  exact (primrec_abs.comp (primrec_tableAt.comp (Primrec.snd.comp Primrec.fst)
    (Primrec.succ.comp Primrec.snd))).to₂

theorem primrec_appLiftTable :
    Primrec (fun p : Nat × List Term × List Term => appLiftTable p.1 p.2.1 p.2.2) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  have hf : Primrec (fun p : (Nat × List Term × List Term) × Nat => tableAt p.1.2.1 p.2) :=
    primrec_tableAt.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hx : Primrec (fun p : (Nat × List Term × List Term) × Nat => tableAt p.1.2.2 p.2) :=
    primrec_tableAt.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact (primrec_app.comp hf hx).to₂

theorem primrec_foldLift : Primrec₂ foldLift := by
  let A := Nat × Code
  let P := Code × Code × List Term × List Term
  let S := A × P
  have hbound : Primrec (fun s : S => s.1.1) := Primrec.fst.comp Primrec.fst
  have hhead : Primrec (fun s : S => s.2.1) := Primrec.fst.comp Primrec.snd
  have harg : Primrec (fun s : S => s.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec (fun s : S => s.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec (fun s : S => s.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hpr : Primrec₂ (fun (a : A) (p : P) => appLiftTable a.1 p.2.2.1 p.2.2.2) :=
    primrec_appLiftTable.comp (hbound.pair (hleft.pair hright))
  have hpc : Primrec₂ (fun (a : A) (p : P) =>
      if Encodable.encode p.1 = Encodable.encode Code.zero then
        ((decodeConst p.2.1).map (varLiftTable a.1)).getD [] else []) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp hhead) (Primrec.const (Encodable.encode Code.zero))
    · have hopt : Primrec (fun s : S => (decodeConst s.2.2.1).map (varLiftTable s.1.1)) :=
        Primrec.option_map (primrec_decodeConst.comp harg)
          ((primrec_varLiftTable.comp (hbound.comp Primrec.fst) Primrec.snd).to₂)
      exact Primrec.option_getD.comp hopt (Primrec.const [])
    · exact Primrec.const []
  have hrf : Primrec₂ (fun (a : A) (p : Code × List Term) => absLiftTable a.1 p.2) :=
    primrec_absLiftTable.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have h := Code.primrec_recOn'
    (c := (Prod.snd : A → Code)) (z := fun _ : A => [])
    (s := fun _ : A => []) (l := fun _ : A => []) (r := fun _ : A => [])
    (pr := fun a p => appLiftTable a.1 p.2.2.1 p.2.2.2)
    (co := fun _ _ => [])
    (pc := fun a p => if Encodable.encode p.1 = Encodable.encode Code.zero then
      ((decodeConst p.2.1).map (varLiftTable a.1)).getD [] else [])
    (rf := fun a p => absLiftTable a.1 p.2)
    Primrec.snd (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_liftFrom : Primrec₂ liftFrom := by
  have hb : Primrec (fun p : Nat × Term => p.1 + termSize p.2) :=
    Primrec.nat_add.comp Primrec.fst (primrec_termSize.comp Primrec.snd)
  have hc : Primrec (fun p : Nat × Term => encodeTerm p.2) := primrec_encodeTerm.comp Primrec.snd
  have ht := primrec_foldLift.comp hb hc
  have hi := primrec_tableAt.comp ht (Primrec.fst : Primrec (fun p : Nat × Term => p.1))
  apply hi.of_eq
  intro p
  exact foldLift_correct p.2 (p.1 + termSize p.2) p.1 (le_refl _)


theorem primrec_liftBy : Primrec₂ liftBy := by
  have hstep : Primrec₂ (fun (_ : Term) (p : Nat × Term) => liftFrom 0 p.2) :=
    primrec_liftFrom.comp (Primrec.const 0) (Primrec.snd.comp Primrec.snd)
  have hrec := Primrec.nat_rec Primrec.id hstep
  have h := hrec.comp (Primrec.snd : Primrec (fun p : Nat × Term => p.2)) Primrec.fst
  apply h.of_eq
  intro p
  rcases p with ⟨n, t⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [id_eq] at ih
    simpa [liftBy] using congrArg (liftFrom 0) ih

#print axioms primrec_liftBy
#print axioms primrec_liftFrom
#print axioms foldLift_correct

end LambdaTuring
