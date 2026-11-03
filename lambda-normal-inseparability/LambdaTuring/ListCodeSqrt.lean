/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The square-root recurrence proof adapts the `sqrt` proof in
Mathlib/Computability/Primrec/List.lean, copyright 2018 Mario Carneiro,
released under Apache 2.0.
-/
module

public import LambdaTuring.ListCodeArithmetic
public meta import LambdaTuring.ListCodeArithmetic

@[expose] public section

namespace LambdaTuring

def listCodeIfPos (test yes no : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  .comp (.case no (.comp yes .tail)) (.cons test .id)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeIfPos_eval (test yes no : Turing.ToPartrec.Code)
    (xs : List Nat) (t a b : Nat)
    (ht : test.eval xs = Part.some [t])
    (hy : yes.eval xs = Part.some [a])
    (hn : no.eval xs = Part.some [b]) :
    (listCodeIfPos test yes no).eval xs = Part.some [if t = 0 then b else a] := by
  cases t with
  | zero =>
    simp [listCodeIfPos, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.cons_eval,
      Turing.ToPartrec.Code.id_eval, Turing.ToPartrec.Code.case_eval, ht, hn, Bind.bind]
  | succ t =>
    simp [listCodeIfPos, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.cons_eval,
      Turing.ToPartrec.Code.id_eval, Turing.ToPartrec.Code.case_eval,
      Turing.ToPartrec.Code.tail_eval, ht, hy, Bind.bind]

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSecond_eval_general (a b : Nat) (v : List Nat) :
    listCodeSecond.eval (a :: b :: v) = Part.some [b] := by
  simp [listCodeSecond, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.head_eval,
    Turing.ToPartrec.Code.tail_eval, Bind.bind]

def listCodeSuccOf (F : Turing.ToPartrec.Code) : Turing.ToPartrec.Code := .comp .succ F

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSuccOf_eval (F : Turing.ToPartrec.Code) (xs : List Nat) (a : Nat)
    (hf : F.eval xs = Part.some [a]) : (listCodeSuccOf F).eval xs = Part.some [a+1] := by
  simp [listCodeSuccOf, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.succ_eval, hf, Bind.bind]

def listCodeSqrtIndex : Turing.ToPartrec.Code := listCodeSuccOf .head
def listCodeSqrtNext : Turing.ToPartrec.Code := listCodeSuccOf listCodeSecond
def listCodeSqrtSquare : Turing.ToPartrec.Code :=
  listCodeBinary listCodeMul listCodeSqrtNext listCodeSqrtNext
def listCodeSqrtCompare : Turing.ToPartrec.Code :=
  listCodeBinary listCodeSub listCodeSqrtIndex listCodeSqrtSquare
def listCodeSqrtStep : Turing.ToPartrec.Code :=
  listCodeIfPos listCodeSqrtCompare listCodeSecond listCodeSqrtNext

theorem listCodeSqrtStep_eval (a b : Nat) (v : List Nat) :
    listCodeSqrtStep.eval (a :: b :: v) =
      Part.some [if a+1 < (b+1)*(b+1) then b else b+1] := by
  have hi : listCodeSqrtIndex.eval (a :: b :: v) = Part.some [a+1] := by
    apply listCodeSuccOf_eval
    simp [Turing.ToPartrec.Code.head_eval]
  have hn : listCodeSqrtNext.eval (a :: b :: v) = Part.some [b+1] :=
    listCodeSuccOf_eval _ _ _ (listCodeSecond_eval_general a b v)
  have hs : listCodeSqrtSquare.eval (a :: b :: v) = Part.some [(b+1)*(b+1)] := by
    apply listCodeBinary_eval listCodeMul listCodeSqrtNext listCodeSqrtNext _ (b+1) (b+1)
    · exact hn
    · exact hn
    · simpa using listCodeMul_eval_general (b+1) [b+1]
  have hc : listCodeSqrtCompare.eval (a :: b :: v) =
      Part.some [(b+1)*(b+1)-(a+1)] := by
    apply listCodeBinary_eval listCodeSub listCodeSqrtIndex listCodeSqrtSquare _ (a+1) ((b+1)*(b+1))
    · exact hi
    · exact hs
    · simpa using listCodeSub_eval_general (a+1) [(b+1)*(b+1)]
  have h := listCodeIfPos_eval listCodeSqrtCompare listCodeSecond listCodeSqrtNext
    (a :: b :: v) ((b+1)*(b+1)-(a+1)) b (b+1) hc (listCodeSecond_eval_general a b v) hn
  by_cases hab : a+1 < (b+1)*(b+1)
  · have hp : (b+1)*(b+1)-(a+1) ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hab)
    simpa [listCodeSqrtStep, hab, hp] using h
  · have hz : (b+1)*(b+1)-(a+1) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hab)
    simpa [listCodeSqrtStep, hab, hz] using h

theorem sqrt_by_rec (n : Nat) : n.sqrt =
    Nat.rec 0 (fun x y => if x+1 < (y+1)*(y+1) then y else y+1) n := by
  symm
  induction n with
  | zero => simp
  | succ n ih =>
    dsimp
    rw [ih]
    split_ifs with h
    · exact le_antisymm (Nat.sqrt_le_sqrt (Nat.le_succ _)) (Nat.lt_succ_iff.1 <| Nat.sqrt_lt.2 h)
    · exact Nat.eq_sqrt.2
        ⟨not_lt.1 h, Nat.sqrt_lt.1 <| Nat.lt_succ_iff.2 <| Nat.sqrt_succ_le_succ_sqrt _⟩

def listCodeSqrt : Turing.ToPartrec.Code := .prec .zero listCodeSqrtStep

theorem listCodeSqrt_eval (n : Nat) (v : List Nat) :
    listCodeSqrt.eval (n :: v) = Part.some [n.sqrt] := by
  have h := listCode_prec_eval .zero listCodeSqrtStep
    (fun _ => 0) (fun a b _ => if a+1 < (b+1)*(b+1) then b else b+1)
    (by intro v; simp [Turing.ToPartrec.Code.zero_eval])
    (fun a b v => listCodeSqrtStep_eval a b v) n v
  rw [← sqrt_by_rec] at h
  exact h

#print axioms listCodeSqrt_eval
end LambdaTuring
