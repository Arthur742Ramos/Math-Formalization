/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.UnaryInputEncoding
public meta import LambdaTuring.UnaryInputEncoding
public import LambdaTuring.ListCodeSearch
public meta import LambdaTuring.ListCodeSearch

@[expose] public section

namespace LambdaTuring

def listCodeDouble : Turing.ToPartrec.Code := listCodeBinary listCodeAdd .head .head

theorem listCodeDouble_eval (a : Nat) (v : List Nat) :
    listCodeDouble.eval (a :: v) = Part.some [a + a] := by
  apply listCodeBinary_eval listCodeAdd .head .head _ a a (a+a)
  · simp [Turing.ToPartrec.Code.head_eval]
  · simp [Turing.ToPartrec.Code.head_eval]
  · exact listCodeAdd_eval a a

def listCodePow2 : Turing.ToPartrec.Code :=
  .prec (.comp .succ .zero) (.comp listCodeDouble .tail)

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
theorem listCodePow2_eval (n : Nat) (v : List Nat) :
    listCodePow2.eval (n :: v) = Part.some [2 ^ n] := by
  have h := listCode_prec_eval (.comp .succ .zero) (.comp listCodeDouble .tail)
    (fun _ => 1) (fun _ b _ => b+b)
    (by intro v; simp [Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.succ_eval,
      Turing.ToPartrec.Code.zero_eval, Bind.bind])
    (by intro a b v; simp [Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.tail_eval,
      listCodeDouble_eval, Bind.bind, Part.bind_some]) n v
  have hr : Nat.rec 1 (fun _ b => b+b) n = 2 ^ n := by
    clear h
    induction n with
    | zero => rfl
    | succ n ih => simp [ih, pow_succ, Nat.mul_comm, two_mul]
  simpa [listCodePow2, hr] using h

def listCodePow2Next : Turing.ToPartrec.Code :=
  .comp listCodePow2 (listCodeSuccOf .head)

attribute [-simp] Part.bind_eq_bind Part.map_eq_map Part.pure_eq_some in
set_option backward.isDefEq.respectTransparency false in
theorem listCodePow2Next_eval (k t : Nat) (v : List Nat) :
    listCodePow2Next.eval (k :: t :: v) = Part.some [2 ^ (k+1)] := by
  have hs : (listCodeSuccOf .head).eval (k :: t :: v) = Part.some [k+1] := by
    apply listCodeSuccOf_eval
    simp [Turing.ToPartrec.Code.head_eval]
  simp [listCodePow2Next, Turing.ToPartrec.Code.comp_eval, hs, listCodePow2_eval, Bind.bind, Part.bind_some]

def listCodeRecoveryTest : Turing.ToPartrec.Code :=
  listCodeBinary listCodeSub listCodePow2Next (listCodeSuccOf listCodeSecond)

theorem listCodeRecoveryTest_eval (k t : Nat) (v : List Nat) :
    listCodeRecoveryTest.eval (k :: t :: v) = Part.some [t+1 - 2^(k+1)] := by
  apply listCodeBinary_eval listCodeSub listCodePow2Next (listCodeSuccOf listCodeSecond)
    _ (2^(k+1)) (t+1) (t+1 - 2^(k+1))
  · exact listCodePow2Next_eval k t v
  · exact listCodeSuccOf_eval _ _ _ (listCodeSecond_eval_general k t v)
  · simpa using listCodeSub_eval_general (2^(k+1)) [t+1]

def listCodeRecoverUnary : Turing.ToPartrec.Code := .rfind listCodeRecoveryTest

theorem listCodeRecoverUnary_eval (n : Nat) :
    listCodeRecoverUnary.eval [onesNumber n] = Part.some [n] := by
  let f : Nat → Part Nat := fun k => Part.some (onesNumber n + 1 - 2^(k+1))
  have hf (k : Nat) : listCodeRecoveryTest.eval (k :: [onesNumber n]) =
      (f k).map (fun r => [r]) := by
    simpa [f] using listCodeRecoveryTest_eval k (onesNumber n) []
  have hfind := listCode_rfind_partial listCodeRecoveryTest f [onesNumber n] hf
  have hm : n ∈ Nat.rfind (fun k => (f k).map (fun r => r = 0)) := by
    apply Nat.mem_rfind.2
    constructor
    · simp [f, onesNumber_add_one]
    · intro k hk
      have hpow : 2^(k+1) < 2^(n+1) := by
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
      have hne : onesNumber n + 1 - 2^(k+1) ≠ 0 := by
        rw [onesNumber_add_one]
        exact Nat.ne_of_gt (Nat.sub_pos_of_lt hpow)
      simp [f, hne]
  have heq : Nat.rfind (fun k => (f k).map (fun r => r = 0)) = Part.some n :=
    Part.eq_some_iff.2 hm
  rw [heq] at hfind
  simpa [listCodeRecoverUnary] using hfind

def compileRecoveredListCode (c : Nat.Partrec.Code) : Turing.ToPartrec.Code :=
  .comp (compileListCodeTotal c) listCodeRecoverUnary

set_option backward.isDefEq.respectTransparency false in
theorem compileRecoveredListCode_eval (c : Nat.Partrec.Code) (n : Nat) :
    (compileRecoveredListCode c).eval [onesNumber n] =
      (Nat.Partrec.Code.eval c n).map (fun r => [r]) := by
  change (listCodeRecoverUnary.eval [onesNumber n]).bind (compileListCodeTotal c).eval = _
  rw [listCodeRecoverUnary_eval, Part.bind_some]
  exact (compileListCodeTotal_sound c) n

#print axioms listCodeRecoverUnary_eval
#print axioms compileRecoveredListCode_eval
end LambdaTuring
