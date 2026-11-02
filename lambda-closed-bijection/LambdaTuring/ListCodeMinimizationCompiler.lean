/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ListCodeSearch
public meta import LambdaTuring.ListCodeSearch

@[expose] public section

namespace LambdaTuring

def listCodeSearchArg : Turing.ToPartrec.Code :=
  listCodeBinary listCodeNatPair listCodeSecond (listCodeBinary listCodeAdd .head listCodeThird)
def listCodeSearchTest (G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code := .comp G listCodeSearchArg
def listCodeSearchInput : Turing.ToPartrec.Code := .cons listCodeUnpairLeft listCodeUnpairRight
def listCodeSearchFromZero (G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  .comp (.rfind (listCodeSearchTest G)) listCodeSearchInput
def listCodeMinimize (G : Turing.ToPartrec.Code) : Turing.ToPartrec.Code :=
  .comp listCodeAdd (.cons (listCodeSearchFromZero G) listCodeUnpairRight)

theorem listCodeSearchArg_eval (k a m : Nat) :
    listCodeSearchArg.eval [k,a,m] = Part.some [Nat.pair a (k+m)] := by
  apply listCodeBinary_eval listCodeNatPair listCodeSecond _ [k,a,m] a (k+m)
  · simpa using listCodeSecond_eval_general k a [m]
  · apply listCodeBinary_eval listCodeAdd .head listCodeThird [k,a,m] k m
    · simp [Turing.ToPartrec.Code.head_eval]
    · simpa using listCodeThird_eval k a [m]
    · exact listCodeAdd_eval k m
  · exact listCodeNatPair_eval a (k+m)

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSearchTest_eval {G : Turing.ToPartrec.Code} {g : Nat →. Nat}
    (hg : ListCodeRepresents G g) (k a m : Nat) :
    (listCodeSearchTest G).eval [k,a,m] = (g (Nat.pair a (k+m))).map (fun r => [r]) := by
  simp [listCodeSearchTest, Turing.ToPartrec.Code.comp_eval, listCodeSearchArg_eval, Bind.bind]
  exact hg _

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSearchInput_eval (n : Nat) :
    listCodeSearchInput.eval [n] = Part.some [n.unpair.1, n.unpair.2] := by
  simp [listCodeSearchInput, Turing.ToPartrec.Code.cons_eval, listCodeUnpairLeft_eval,
    listCodeUnpairRight_eval, Bind.bind]

set_option backward.isDefEq.respectTransparency false in
theorem listCodeSearchFromZero_eval {G : Turing.ToPartrec.Code} {g : Nat →. Nat}
    (hg : ListCodeRepresents G g) (n : Nat) :
    (listCodeSearchFromZero G).eval [n] =
      (Nat.rfind (fun k => (g (Nat.pair n.unpair.1 (k+n.unpair.2))).map (fun r => r = 0))).map
        (fun r => [r]) := by
  have h := listCode_rfind_partial (listCodeSearchTest G)
    (fun k => g (Nat.pair n.unpair.1 (k+n.unpair.2))) [n.unpair.1, n.unpair.2]
    (fun k => listCodeSearchTest_eval hg k n.unpair.1 n.unpair.2)
  simpa [listCodeSearchFromZero, Turing.ToPartrec.Code.comp_eval,
    listCodeSearchInput_eval, Bind.bind] using h

set_option backward.isDefEq.respectTransparency false in
theorem listCodeMinimize_represents {G : Turing.ToPartrec.Code} {g : Nat.Partrec.Code}
    (hg : ListCodeRepresents G (Nat.Partrec.Code.eval g)) :
    ListCodeRepresents (listCodeMinimize G) (Nat.Partrec.Code.eval (.rfind' g)) := by
  intro n
  have hs := listCodeSearchFromZero_eval hg n
  have ho := listCodeUnpairRight_eval n
  simp only [listCodeMinimize, Turing.ToPartrec.Code.comp_eval,
    Turing.ToPartrec.Code.cons_eval, hs, ho, Bind.bind, Part.bind_map,
    Part.bind_some, List.headI_cons]
  simp [listCodeAdd_eval, Nat.Partrec.Code.eval,
    Nat.unpaired, Part.bind_some_eq_map, Part.map_map, Function.comp_def]

#print axioms listCodeMinimize_represents
end LambdaTuring
