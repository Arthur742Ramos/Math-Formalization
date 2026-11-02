/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.LiftTable
public meta import LambdaTuring.LiftTable
public import LambdaTuring.BetaStepComputable
public meta import LambdaTuring.BetaStepComputable

@[expose] public section

namespace LambdaTuring
open Nat.Partrec

def varSubstTable (bound : Nat) (value : Term) (n : Nat) : List Term :=
  (List.range (bound + 1)).map fun depth =>
    if n = depth then liftBy depth value else .var (if depth < n then n - 1 else n)

def foldSubst (bound : Nat) (value : Term) (c : Code) : List Term :=
  Code.recOn c [] [] [] []
    (fun _ _ a b => appLiftTable bound a b)
    (fun _ _ _ _ => [])
    (fun f g _ _ => if Encodable.encode f = Encodable.encode Code.zero then
      ((decodeConst g).map (varSubstTable bound value)).getD [] else [])
    (fun _ body => absLiftTable bound body)

theorem foldSubst_correct (t : Term) (bound depth : Nat) (value : Term)
    (h : depth + termSize t ≤ bound) :
    tableAt (foldSubst bound value (encodeTerm t)) depth = substAt depth value t := by
  induction t generalizing depth with
  | var n =>
    have hi : depth ≤ bound := by simp [termSize] at h; omega
    change tableAt (if Encodable.encode Code.zero = Encodable.encode Code.zero then
      ((decodeConst (Code.const n)).map (varSubstTable bound value)).getD [] else []) depth = _
    simp only [ite_true, decodeConst_const, Option.map_some, Option.getD_some]
    exact tableAt_range_map bound depth _ hi
  | abs t ih =>
    have hi : depth ≤ bound := by simp [termSize] at h; omega
    have hc : depth + 1 + termSize t ≤ bound := by simp [termSize] at h; omega
    change tableAt (absLiftTable bound (foldSubst bound value (encodeTerm t))) depth = _
    rw [tableAt_absLiftTable bound depth _ hi, ih (depth + 1) hc]
    rfl
  | app f x ihf ihx =>
    have hi : depth ≤ bound := by simp [termSize] at h; omega
    have hf : depth + termSize f ≤ bound := by simp [termSize] at h; omega
    have hx : depth + termSize x ≤ bound := by simp [termSize] at h; omega
    change tableAt (appLiftTable bound (foldSubst bound value (encodeTerm f)) (foldSubst bound value (encodeTerm x))) depth = _
    rw [tableAt_appLiftTable bound depth _ _ hi, ihf depth hf, ihx depth hx]
    rfl

theorem primrec_varSubstTable :
    Primrec (fun p : Nat × Term × Nat => varSubstTable p.1 p.2.1 p.2.2) := by
  let P := Nat × Term × Nat
  let Q := P × Nat
  have hn : Primrec (fun q : Q => q.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hv : Primrec (fun q : Q => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun q : Q => q.2) := Primrec.snd
  have hb : Primrec (fun p : P => p.1) := Primrec.fst
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hb))
  have hc : Primrec (fun q : Q => if q.1.2.2 = q.2 then liftBy q.2 q.1.2.1
      else Term.var (if q.2 < q.1.2.2 then q.1.2.2 - 1 else q.1.2.2)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp hn hd
    · exact primrec_liftBy.comp hd hv
    · apply primrec_var.comp
      apply Primrec.ite
      · exact Primrec.nat_lt.comp hd hn
      · exact Primrec.nat_sub.comp hn (Primrec.const 1)
      · exact hn
  exact hc.to₂

theorem primrec_foldSubst :
    Primrec (fun a : Nat × Term × Code => foldSubst a.1 a.2.1 a.2.2) := by
  let A := Nat × Term × Code
  let P := Code × Code × List Term × List Term
  let S := A × P
  have hbound : Primrec (fun s : S => s.1.1) := Primrec.fst.comp Primrec.fst
  have hvalue : Primrec (fun s : S => s.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
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
        ((decodeConst p.2.1).map (varSubstTable a.1 a.2.1)).getD [] else []) := by
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.encode.comp hhead) (Primrec.const (Encodable.encode Code.zero))
    · have hopt : Primrec (fun s : S => (decodeConst s.2.2.1).map (varSubstTable s.1.1 s.1.2.1)) :=
        Primrec.option_map (primrec_decodeConst.comp harg)
          ((primrec_varSubstTable.comp ((hbound.comp Primrec.fst).pair
            ((hvalue.comp Primrec.fst).pair Primrec.snd))).to₂)
      exact Primrec.option_getD.comp hopt (Primrec.const [])
    · exact Primrec.const []
  have hrf : Primrec₂ (fun (a : A) (p : Code × List Term) => absLiftTable a.1 p.2) :=
    primrec_absLiftTable.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have h := Code.primrec_recOn'
    (c := fun a : A => a.2.2) (z := fun _ : A => [])
    (s := fun _ : A => []) (l := fun _ : A => []) (r := fun _ : A => [])
    (pr := fun a p => appLiftTable a.1 p.2.2.1 p.2.2.2)
    (co := fun _ _ => [])
    (pc := fun a p => if Encodable.encode p.1 = Encodable.encode Code.zero then
      ((decodeConst p.2.1).map (varSubstTable a.1 a.2.1)).getD [] else [])
    (rf := fun a p => absLiftTable a.1 p.2)
    (Primrec.snd.comp Primrec.snd) (Primrec.const _) (Primrec.const _) (Primrec.const _) (Primrec.const _)
    hpr (Primrec₂.const _) hpc hrf
  exact h.of_eq (fun _ => rfl)

theorem primrec_substAt :
    Primrec (fun p : Nat × Term × Term => substAt p.1 p.2.1 p.2.2) := by
  have hb : Primrec (fun p : Nat × Term × Term => p.1 + termSize p.2.2) :=
    Primrec.nat_add.comp Primrec.fst (primrec_termSize.comp (Primrec.snd.comp Primrec.snd))
  have hv : Primrec (fun p : Nat × Term × Term => p.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun p : Nat × Term × Term => encodeTerm p.2.2) :=
    primrec_encodeTerm.comp (Primrec.snd.comp Primrec.snd)
  have ht := primrec_foldSubst.comp (hb.pair (hv.pair hc))
  have hi := primrec_tableAt.comp ht (Primrec.fst : Primrec (fun p : Nat × Term × Term => p.1))
  apply hi.of_eq
  intro p
  exact foldSubst_correct p.2.2 (p.1 + termSize p.2.2) p.1 p.2.1 (le_refl _)

theorem primrec_substZero : Primrec₂ (fun value body => substAt 0 value body) :=
  primrec_substAt.comp (Primrec.pair (Primrec.const 0) (Primrec.pair Primrec.fst Primrec.snd))

theorem numericalValue_partrec (t : Term) : Nat.Partrec (numericalValue t) :=
  numericalValue_partrec_of_subst primrec_substZero t

#print axioms primrec_substAt
#print axioms numericalValue_partrec

end LambdaTuring
