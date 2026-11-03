/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.

The primitive-recursion proof below adapts the `prec` case of
Mathlib/Computability/TuringMachine/Config.lean, copyright 2020 Mario Carneiro,
released under Apache 2.0.
-/
module

public import LambdaTuring.ListCodeTuple
public meta import LambdaTuring.ListCodeTuple

@[expose] public section

namespace LambdaTuring

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's list-code recursion combinator implements total primitive
    recursion when its supplied base and step codes have these exact results. -/
theorem listCode_prec_eval (F G : Turing.ToPartrec.Code)
    (f : List Nat → Nat) (g : Nat → Nat → List Nat → Nat)
    (hf : ∀ v, F.eval v = Part.some [f v])
    (hg : ∀ a b v, G.eval (a :: b :: v) = Part.some [g a b v])
    (n : Nat) (v : List Nat) :
    (Turing.ToPartrec.Code.prec F G).eval (n :: v) =
      Part.some [Nat.rec (f v) (fun a b => g a b v) n] := by
  let R : Nat → Nat := fun n => Nat.rec (f v) (fun a b => g a b v) n
  change (Turing.ToPartrec.Code.prec F G).eval (n :: v) = Part.some [R n]
  cases n with
  | zero =>
    simp [Turing.ToPartrec.Code.prec, hf, R, Bind.bind, Part.bind_some]
  | succ n =>
    have hloop : ∀ a b, a + b = n →
      (n.succ :: 0 :: R n.succ :: v : List Nat) ∈
        PFun.fix
          (fun w : List Nat => Part.bind (G.eval (w.headI :: w.tail.tail))
            (fun x => Part.some (if w.tail.headI = 0
              then Sum.inl (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail)
              else Sum.inr (w.headI.succ :: w.tail.headI.pred :: x.headI :: w.tail.tail.tail))))
          (a :: b :: R a :: v) := by
      intro a b e
      induction b generalizing a with
      | zero =>
        refine PFun.mem_fix_iff.2 (Or.inl <| Part.eq_some_iff.1 ?_)
        simp [hg, ← e, R]
      | succ b ih =>
        refine PFun.mem_fix_iff.2 (Or.inr ⟨_, ?_, ih (a + 1) (by omega)⟩)
        simp only [hg, Part.bind_some, List.tail_cons]
        exact Part.mem_some_iff.2 rfl
    have h := Part.eq_some_iff.mpr (hloop 0 n (zero_add n))
    simp [Turing.ToPartrec.Code.prec, Part.bind_assoc, Bind.bind, Part.bind_some]
    simp_all [R]

def listCodeAdd : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.prec .head (.comp .succ .tail)

theorem listCodeAdd_eval_general (a : Nat) (v : List Nat) :
    listCodeAdd.eval (a :: v) = Part.some [a + v.headI] := by
  have h := listCode_prec_eval .head (.comp .succ .tail)
    (fun v => v.headI) (fun _ b _ => b+1)
    (by intro v; simp [Turing.ToPartrec.Code.head_eval])
    (by intro a b v; simp [Turing.ToPartrec.Code.comp_eval,
      Turing.ToPartrec.Code.succ_eval, Turing.ToPartrec.Code.tail_eval, Part.bind_eq_bind])
    a v
  have hr : Nat.rec v.headI (fun _ x => x+1) a = a + v.headI := by
    clear h
    induction a with
    | zero => simp
    | succ a ih => simp [ih, Nat.succ_add]
  simpa [listCodeAdd, hr] using h

theorem listCodeAdd_eval (a b : Nat) :
    listCodeAdd.eval [a,b] = Part.some [a+b] := by
  simpa using listCodeAdd_eval_general a [b]

def listCodeSub : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.prec .head (.comp .pred .tail)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSub_eval_general (a : Nat) (v : List Nat) :
    listCodeSub.eval (a :: v) = Part.some [v.headI - a] := by
  have h := listCode_prec_eval .head (.comp .pred .tail)
    (fun v => v.headI) (fun _ b _ => b.pred)
    (by intro v; simp [Turing.ToPartrec.Code.head_eval])
    (by intro a b v; simp [Turing.ToPartrec.Code.comp_eval,
      Turing.ToPartrec.Code.pred_eval, Turing.ToPartrec.Code.tail_eval, Part.bind_eq_bind])
    a v
  have hr : Nat.rec v.headI (fun _ x => x.pred) a = v.headI - a := by
    clear h
    induction a with
    | zero => simp
    | succ a ih =>
      change (Nat.rec (motive := fun _ => Nat) v.headI (fun _ x => x.pred) a).pred =
        v.headI - (a+1)
      rw [ih, Nat.sub_succ]
  change listCodeSub.eval (a :: v) = Part.some [Nat.rec v.headI (fun _ x => x.pred) a] at h
  rw [hr] at h
  exact h

def listCodeMul : Turing.ToPartrec.Code :=
  Turing.ToPartrec.Code.prec .zero (.comp listCodeAdd .tail)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeMul_eval_general (a : Nat) (v : List Nat) :
    listCodeMul.eval (a :: v) = Part.some [a * v.headI] := by
  have h := listCode_prec_eval .zero (.comp listCodeAdd .tail)
    (fun _ => 0) (fun _ b v => b + v.headI)
    (by intro v; simp [Turing.ToPartrec.Code.zero_eval])
    (by intro a b v; simp [Turing.ToPartrec.Code.comp_eval,
      Turing.ToPartrec.Code.tail_eval, Part.bind_eq_bind, listCodeAdd_eval_general])
    a v
  have hr : Nat.rec 0 (fun _ x => x + v.headI) a = a * v.headI := by
    clear h
    induction a with
    | zero => simp
    | succ a ih => simp [ih, Nat.succ_mul, Nat.add_comm]
  simpa [listCodeMul, hr] using h

/-- Build the two-element argument list and apply a binary list-code program. -/
def listCodeBinary (op F G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  .comp op (.cons F G)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeBinary_eval (op F G : Turing.ToPartrec.Code) (xs : List Nat) (a b c : Nat)
    (hf : F.eval xs = Part.some [a]) (hg : G.eval xs = Part.some [b])
    (hop : op.eval [a,b] = Part.some [c]) :
    (listCodeBinary op F G).eval xs = Part.some [c] := by
  simp [listCodeBinary, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.cons_eval,
    hf, hg, hop, Bind.bind]

def listCodeSecond : Turing.ToPartrec.Code := .comp .head .tail
def listCodeSquareFirst : Turing.ToPartrec.Code := listCodeBinary listCodeMul .head .head
def listCodeSquareSecond : Turing.ToPartrec.Code :=
  listCodeBinary listCodeMul listCodeSecond listCodeSecond
def listCodePairLt : Turing.ToPartrec.Code :=
  listCodeBinary listCodeAdd listCodeSquareSecond .head
def listCodePairGe : Turing.ToPartrec.Code :=
  listCodeBinary listCodeAdd (listCodeBinary listCodeAdd listCodeSquareFirst .head) listCodeSecond
def listCodeNatPair : Turing.ToPartrec.Code :=
  .comp (.case listCodePairGe (.comp listCodePairLt .tail)) (.cons listCodeSub .id)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSecond_eval (a b : Nat) : listCodeSecond.eval [a,b] = Part.some [b] := by
  simp [listCodeSecond, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.head_eval,
    Turing.ToPartrec.Code.tail_eval, Bind.bind]

theorem listCodeSquareFirst_eval (a b : Nat) :
    listCodeSquareFirst.eval [a,b] = Part.some [a*a] := by
  apply listCodeBinary_eval listCodeMul .head .head [a,b] a a (a*a)
  · simp [Turing.ToPartrec.Code.head_eval]
  · simp [Turing.ToPartrec.Code.head_eval]
  · simpa using listCodeMul_eval_general a [a]

theorem listCodeSquareSecond_eval (a b : Nat) :
    listCodeSquareSecond.eval [a,b] = Part.some [b*b] := by
  apply listCodeBinary_eval listCodeMul listCodeSecond listCodeSecond [a,b] b b (b*b)
  · exact listCodeSecond_eval a b
  · exact listCodeSecond_eval a b
  · simpa using listCodeMul_eval_general b [b]

theorem listCodePairLt_eval (a b : Nat) :
    listCodePairLt.eval [a,b] = Part.some [b*b+a] := by
  apply listCodeBinary_eval listCodeAdd listCodeSquareSecond .head [a,b] (b*b) a (b*b+a)
  · exact listCodeSquareSecond_eval a b
  · simp [Turing.ToPartrec.Code.head_eval]
  · exact listCodeAdd_eval (b*b) a

theorem listCodePairGe_eval (a b : Nat) :
    listCodePairGe.eval [a,b] = Part.some [a*a+a+b] := by
  apply listCodeBinary_eval listCodeAdd _ listCodeSecond [a,b] (a*a+a) b (a*a+a+b)
  · apply listCodeBinary_eval listCodeAdd listCodeSquareFirst .head [a,b] (a*a) a (a*a+a)
    · exact listCodeSquareFirst_eval a b
    · simp [Turing.ToPartrec.Code.head_eval]
    · exact listCodeAdd_eval (a*a) a
  · exact listCodeSecond_eval a b
  · exact listCodeAdd_eval (a*a+a) b

set_option backward.isDefEq.respectTransparency false in
theorem listCodeNatPair_eval (a b : Nat) :
    listCodeNatPair.eval [a,b] = Part.some [Nat.pair a b] := by
  have hs : listCodeSub.eval [a,b] = Part.some [b-a] := by
    simpa using listCodeSub_eval_general a [b]
  unfold listCodeNatPair
  simp only [Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.cons_eval,
    Turing.ToPartrec.Code.id_eval, Bind.bind, Part.bind_some, hs, List.headI_cons]
  rw [Turing.ToPartrec.Code.case_eval]
  by_cases hab : a < b
  · have hpos : 0 < b-a := Nat.sub_pos_iff_lt.mpr hab
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    simp [hk, Nat.pair, hab, Turing.ToPartrec.Code.comp_eval,
      Turing.ToPartrec.Code.tail_eval, Bind.bind, listCodePairLt_eval]
  · have hz : b-a = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hab)
    simp [hz, Nat.pair, hab, listCodePairGe_eval]

#print axioms listCode_prec_eval
#print axioms listCodeAdd_eval
#print axioms listCodeSub_eval_general
#print axioms listCodeMul_eval_general
#print axioms listCodeNatPair_eval
end LambdaTuring
