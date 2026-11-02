/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.CodedIsomorphism
public meta import LambdaTuring.CodedIsomorphism
@[expose] public section
namespace LambdaTuring

/-- A syntactically injective tag on a recursive code, without changing the
partial numerical function it computes. -/
def unaryCodePadding (p : Nat.Partrec.Code × Nat) : Nat.Partrec.Code :=
  Nat.Partrec.Code.curry (.comp p.1 .right) p.2

theorem unaryCodePadding_primrec : Primrec unaryCodePadding := by
  have hc : Primrec (fun p : Nat.Partrec.Code × Nat => Nat.Partrec.Code.comp p.1 .right) :=
    Nat.Partrec.Code.primrec₂_comp.comp Primrec.fst (Primrec.const _)
  exact Nat.Partrec.Code.primrec₂_curry.comp hc Primrec.snd

theorem unaryCodePadding_injective : Function.Injective unaryCodePadding := by
  intro p q h
  have hh := Nat.Partrec.Code.curry_inj h
  have he : p.1 = q.1 := by
    exact Nat.Partrec.Code.comp.inj hh.1 |>.1
  exact Prod.ext he hh.2

theorem unaryCodePadding_eval (c : Nat.Partrec.Code) (k x : Nat) :
    Nat.Partrec.Code.eval (unaryCodePadding (c, k)) x = Nat.Partrec.Code.eval c x := by
  rw [unaryCodePadding, Nat.Partrec.Code.eval_curry]
  change (Nat.Partrec.Code.eval .right (Nat.pair k x)).bind (Nat.Partrec.Code.eval c) = _
  simp only [Nat.Partrec.Code.eval, Nat.unpair_pair, PFun.coe_val]
  exact Part.bind_some x (Nat.Partrec.Code.eval c)

#print axioms unaryCodePadding_primrec
#print axioms unaryCodePadding_injective
#print axioms unaryCodePadding_eval
end LambdaTuring
