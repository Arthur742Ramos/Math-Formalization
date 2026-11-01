/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodePartialRecursion
public meta import LambdaTuring.ListCodePartialRecursion

@[expose] public section

namespace LambdaTuring

def listCodeThird : Turing.ToPartrec.Code := .comp .head (.comp .tail .tail)
def listCodeRecStepArg : Turing.ToPartrec.Code :=
  listCodeBinary listCodeNatPair listCodeThird (listCodeBinary listCodeNatPair .head listCodeSecond)
def listCodeRecInput : Turing.ToPartrec.Code := .cons listCodeUnpairRight listCodeUnpairLeft
def listCodeRecBase (F : Turing.ToPartrec.Code) : Turing.ToPartrec.Code := .comp F .head
def listCodeRecStep (G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code := .comp G listCodeRecStepArg
def listCodeRecursion (F G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  .comp (.prec (listCodeRecBase F) (listCodeRecStep G)) listCodeRecInput

set_option backward.isDefEq.respectTransparency false in
theorem listCodeThird_eval (i x : Nat) (v : List Nat) :
    listCodeThird.eval (i :: x :: v) = Part.some [v.headI] := by
  simp [listCodeThird, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.head_eval,
    Turing.ToPartrec.Code.tail_eval, Bind.bind]

theorem listCodeRecStepArg_eval (i x : Nat) (v : List Nat) :
    listCodeRecStepArg.eval (i :: x :: v) = Part.some [Nat.pair v.headI (Nat.pair i x)] := by
  apply listCodeBinary_eval listCodeNatPair listCodeThird _ (i :: x :: v) v.headI (Nat.pair i x)
  · exact listCodeThird_eval i x v
  · apply listCodeBinary_eval listCodeNatPair .head listCodeSecond (i :: x :: v) i x
    · simp [Turing.ToPartrec.Code.head_eval]
    · exact listCodeSecond_eval_general i x v
    · exact listCodeNatPair_eval i x
  · exact listCodeNatPair_eval v.headI (Nat.pair i x)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeRecInput_eval (n : Nat) :
    listCodeRecInput.eval [n] = Part.some [n.unpair.2, n.unpair.1] := by
  simp [listCodeRecInput, Turing.ToPartrec.Code.cons_eval, listCodeUnpairRight_eval,
    listCodeUnpairLeft_eval, Bind.bind]

set_option backward.isDefEq.respectTransparency false in
theorem listCodeRecBase_eval {F : Turing.ToPartrec.Code} {f : Nat →. Nat}
    (hf : ListCodeRepresents F f) (v : List Nat) :
    (listCodeRecBase F).eval v = (f v.headI).map (fun r => [r]) := by
  simp [listCodeRecBase, Turing.ToPartrec.Code.comp_eval, Turing.ToPartrec.Code.head_eval,
    Bind.bind]
  exact hf _

set_option backward.isDefEq.respectTransparency false in
theorem listCodeRecStep_eval {G : Turing.ToPartrec.Code} {g : Nat →. Nat}
    (hg : ListCodeRepresents G g) (i x : Nat) (v : List Nat) :
    (listCodeRecStep G).eval (i :: x :: v) =
      (g (Nat.pair v.headI (Nat.pair i x))).map (fun r => [r]) := by
  simp [listCodeRecStep, Turing.ToPartrec.Code.comp_eval, listCodeRecStepArg_eval,
    Bind.bind]
  exact hg _

set_option backward.isDefEq.respectTransparency false in
theorem listCodeRecursion_represents {F G : Turing.ToPartrec.Code}
    {f g : Nat.Partrec.Code}
    (hf : ListCodeRepresents F (Nat.Partrec.Code.eval f))
    (hg : ListCodeRepresents G (Nat.Partrec.Code.eval g)) :
    ListCodeRepresents (listCodeRecursion F G) (Nat.Partrec.Code.eval (.prec f g)) := by
  intro n
  have hprec := listCode_prec_partial (listCodeRecBase F) (listCodeRecStep G)
    (fun v => Nat.Partrec.Code.eval f v.headI)
    (fun i x v => Nat.Partrec.Code.eval g (Nat.pair v.headI (Nat.pair i x)))
    (listCodeRecBase_eval hf) (listCodeRecStep_eval hg) n.unpair.2 [n.unpair.1]
  simp [listCodeRecursion, Turing.ToPartrec.Code.comp_eval, listCodeRecInput_eval, Bind.bind]
  rw [hprec]
  rfl

#print axioms listCodeRecursion_represents
end LambdaTuring
