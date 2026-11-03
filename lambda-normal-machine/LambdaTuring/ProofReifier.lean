/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.EffectiveCode
public meta import LambdaTuring.EffectiveCode
public import LambdaTuring.FastPpred
public meta import LambdaTuring.FastPpred
public import LambdaTuring.CPSBottom
public meta import LambdaTuring.CPSBottom
public import Lean
public meta import Lean
import all Mathlib.Computability.Primrec.Basic
import all Mathlib.Computability.Partrec

@[expose] public section

open Lean Meta Elab Term
open LambdaTuring.EffectiveCode

namespace LambdaTuring.ReifierManual

/-- Explicit witnesses avoid inspecting opaque imported theorem bodies. -/
def identity : TotalWitness (fun n => n) := ⟨Nat.Partrec.Code.id, Nat.Partrec.Code.eval_id⟩

def add : TotalWitness (Nat.unpaired (· + ·)) :=
  (TotalWitness.prec identity (TotalWitness.comp TotalWitness.succ
    (TotalWitness.comp TotalWitness.right TotalWitness.right))).ofEq (by
      intro p
      simp only [Nat.unpaired, Nat.unpair_pair]
      generalize p.unpair.1 = a
      generalize p.unpair.2 = n
      induction n with
      | zero => simp only [Nat.rec_zero, Nat.add_zero]
      | succ n ih => simp only [Nat.add_succ, ih])

def sub : TotalWitness (Nat.unpaired (· - ·)) :=
  (TotalWitness.prec identity (TotalWitness.comp
    ⟨predCode, eval_predCode⟩ (TotalWitness.comp TotalWitness.right TotalWitness.right))).ofEq (by
      intro p
      simp only [Nat.unpaired, Nat.unpair_pair]
      generalize p.unpair.1 = a
      generalize p.unpair.2 = n
      induction n with
      | zero => simp only [Nat.rec_zero, Nat.sub_zero]
      | succ n ih => simp only [Nat.sub_succ, ih])

def mul : TotalWitness (Nat.unpaired (· * ·)) :=
  (TotalWitness.prec TotalWitness.zero (TotalWitness.comp add
    (TotalWitness.pair TotalWitness.left (TotalWitness.comp TotalWitness.right TotalWitness.right)))).ofEq (by
      intro p
      simp only [Nat.unpaired, Nat.unpair_pair]
      generalize p.unpair.1 = a
      generalize p.unpair.2 = n
      induction n with
      | zero => simp only [Nat.rec_zero, Nat.mul_zero]
      | succ n ih => simp only [Nat.mul_succ, ih, Nat.add_comm])

def bottom : Witness (fun _ : Nat => Part.none) :=
  ⟨LambdaTuring.bottomCode, funext LambdaTuring.bottomCode_eval⟩

end LambdaTuring.ReifierManual

meta partial def unfoldProofHead (p : Expr) : MetaM Expr := do
  let p ← withReducible <| whnf p
  let args := p.getAppArgs
  match p.getAppFn with
  | .proj typeName idx body =>
    let body' ← unfoldProofHead body
    return mkAppN (.proj typeName idx body') args
  | .const name levels =>
    let info ← getConstInfo name
    let body? := match info with
      | .thmInfo t => some t.value
      | .defnInfo d => some d.value
      | _ => none
    let some body := body? | throwError "unsupported proof constant {name}"
    return mkAppN (body.instantiateLevelParams info.levelParams levels) args
  | x => throwError "unsupported unfolding head {repr x}"

/-- Search a closed proof term for an explicit equality of the two encoded
functions. Any returned equality is still checked by the kernel. -/
meta partial def findFunctionEq (e left right : Expr) : MetaM (Option Expr) := do
  if e.getAppFn.isConstOf ``funext && !e.hasLooseBVars then
    try
      let ty ← withReducible <| whnf (← inferType e)
      let args := ty.getAppArgs
      if ty.getAppFn.isConstOf ``Eq && args.size == 3 then
        if (← isDefEq args[1]! left) && (← isDefEq args[2]! right) then return some e
        if (← isDefEq args[1]! right) && (← isDefEq args[2]! left) then
          return some (← mkAppM ``Eq.symm #[e])
    catch _ => pure ()
  let children := match e with
    | .app f x => #[f, x]
    | .lam _ t b _ | .forallE _ t b _ => #[t, b]
    | .letE _ t v b _ => #[t, v, b]
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  for child in children do
    if let some h ← findFunctionEq child left right then return some h
  return none

/-- Experimental elaborator. It emits a data-bearing witness and lets Lean's
kernel check its semantics; it is not an elimination of `Prop` at runtime. -/
meta partial def reifyTotalProof (p : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "reifier depth exceeded"
  let p ← withReducible <| whnf p
  let args := p.getAppArgs
  if let .proj _ _ body := p.getAppFn then
    let body ← withReducible <| whnf body
    if body.getAppFn.isConstOf ``Eq.rec then
      let source := args.back!
      let srcTy ← withTransparency .all <| whnf (← inferType source)
      let dstTy ← withTransparency .all <| whnf (← inferType p)
      unless srcTy.getAppFn.isConstOf ``Nat.Primrec && dstTy.getAppFn.isConstOf ``Nat.Primrec do
        throwError "equivalence transport is not primitive-recursive"
      let srcFn := srcTy.getAppArgs.back!
      let dstFn := dstTy.getAppArgs.back!
      let a ← reifyTotalProof source (fuel - 1)
      if ← isDefEq srcFn dstFn then return a
      let some h ← findFunctionEq body srcFn dstFn |
        throwError "no explicit encoded-function equality in equivalence proof"
      let h' ← mkAppM ``congrFun #[h]
      return ← mkAppM ``TotalWitness.ofEq #[a, h']
  let .const name _ := p.getAppFn | return ← reifyTotalProof (← unfoldProofHead p) (fuel - 1)
  let last (i : Nat) := args[args.size - i]!
  if name == ``Eq.rec then
    let minor := args[3]!
    let eqProof := args[5]!
    let a ← reifyTotalProof minor (fuel - 1)
    let srcTy ← withTransparency .all <| whnf (← inferType minor)
    let srcFn := srcTy.getAppArgs.back!
    let eqInner := eqProof.getAppArgs.back!
    let eqTy ← withTransparency .all <| whnf (← inferType eqInner)
    let oldFn := eqTy.getAppArgs[1]!
    let oldTy ← inferType oldFn
    return ← withLocalDeclD `value oldTy fun v => do
      let newFn := srcFn.replace fun e => if e == oldFn then some v else none
      if newFn == srcFn then throwError "transport source does not contain equality lhs\nsource: {srcFn}\nlhs: {oldFn}\nequality: {eqProof}"
      let mapper ← mkLambdaFVars #[v] newFn
      let eqMapped ← mkAppM ``congrArg #[mapper, eqInner]
      let pointwise ← mkAppM ``congrFun #[eqMapped]
      return ← mkAppM ``TotalWitness.ofEq #[a, pointwise]
  if name == ``Nat.Primrec.zero then return mkConst ``TotalWitness.zero
  if name == ``Nat.Primrec.succ then return mkConst ``TotalWitness.succ
  if name == ``Nat.Primrec.add then return mkConst ``LambdaTuring.ReifierManual.add
  if name == ``Nat.Primrec.sub then return mkConst ``LambdaTuring.ReifierManual.sub
  if name == ``Nat.Primrec.mul then return mkConst ``LambdaTuring.ReifierManual.mul
  if name == ``Nat.Primrec.left then return mkConst ``TotalWitness.left
  if name == ``Nat.Primrec.right then return mkConst ``TotalWitness.right
  if name == ``Nat.Primrec.const then return ← mkAppM ``TotalWitness.const #[last 1]
  if name == ``Nat.Primrec.pair || name == ``Nat.Primrec.comp || name == ``Nat.Primrec.prec then
    let a ← reifyTotalProof (last 2) (fuel - 1)
    let b ← reifyTotalProof (last 1) (fuel - 1)
    let ctor := if name == ``Nat.Primrec.pair then ``TotalWitness.pair else
      if name == ``Nat.Primrec.comp then ``TotalWitness.comp else ``TotalWitness.prec
    return ← mkAppM ctor #[a, b]
  if name == ``Nat.Primrec.of_eq then
    let a ← reifyTotalProof (last 2) (fuel - 1)
    return ← mkAppM ``TotalWitness.ofEq #[a, last 1]
  reifyTotalProof (← unfoldProofHead p) (fuel - 1)

elab "total_code_from% " p:term : term => do
  let e ← elabTerm p none
  let proofType ← withTransparency .all <| whnf (← inferType e)
  unless proofType.getAppFn.isConstOf ``Nat.Primrec do
    throwError "expected a Nat.Primrec proof"
  let f ← instantiateMVars proofType.getAppArgs.back!
  if f.hasMVar then throwError "input total function has unresolved metavariables"
  let expected := mkApp (mkConst ``TotalWitness) f
  let result ← reifyTotalProof e 500
  unless ← isDefEq (← inferType result) expected do
    throwError "reified total witness does not target the input function"
  return result

meta partial def reifyPartialProof (p : Expr) (fuel : Nat) : MetaM Expr := do
  if fuel == 0 then throwError "partial reifier depth exceeded"
  let p ← withReducible <| whnf p
  let args := p.getAppArgs
  let .const name _ := p.getAppFn | return ← reifyPartialProof (← unfoldProofHead p) (fuel - 1)
  let last (i : Nat) := args[args.size - i]!
  if name == ``Eq.rec then throwError "partial transport type: {← inferType p}\nminor: {args[3]!}\nminor type: {← inferType args[3]!}\nequality: {args[5]!}"
  if name == ``Nat.Partrec.ppred then return mkConst ``ppredWitness
  if name == ``Nat.Partrec.none then return mkConst ``LambdaTuring.ReifierManual.bottom
  if name == ``Nat.Partrec.zero then return mkConst ``LambdaTuring.EffectiveCode.zero
  if name == ``Nat.Partrec.succ then return mkConst ``LambdaTuring.EffectiveCode.succ
  if name == ``Nat.Partrec.left then return mkConst ``LambdaTuring.EffectiveCode.left
  if name == ``Nat.Partrec.right then return mkConst ``LambdaTuring.EffectiveCode.right
  if name == ``Nat.Partrec.pair || name == ``Nat.Partrec.comp || name == ``Nat.Partrec.prec then
    let a ← reifyPartialProof (last 2) (fuel - 1)
    let b ← reifyPartialProof (last 1) (fuel - 1)
    let ctor := if name == ``Nat.Partrec.pair then ``LambdaTuring.EffectiveCode.pair else
      if name == ``Nat.Partrec.comp then ``LambdaTuring.EffectiveCode.comp else
        ``LambdaTuring.EffectiveCode.prec
    return ← mkAppM ctor #[a, b]
  if name == ``Nat.Partrec.rfind then
    let a ← reifyPartialProof (last 1) (fuel - 1)
    return ← mkAppM ``LambdaTuring.EffectiveCode.rfind #[a]
  if name == ``Nat.Partrec.of_eq then
    let a ← reifyPartialProof (last 2) (fuel - 1)
    let h ← mkAppM ``funext #[last 1]
    return ← mkAppM ``LambdaTuring.EffectiveCode.ofEq #[a, h]
  if name == ``Nat.Partrec.of_primrec then
    let a ← reifyTotalProof (last 1) (fuel - 1)
    return ← mkAppM ``TotalWitness.toWitness #[a]
  reifyPartialProof (← unfoldProofHead p) (fuel - 1)

elab "partial_code_from% " p:term : term => do
  let e ← elabTerm p none
  let proofType ← withTransparency .all <| whnf (← inferType e)
  unless proofType.getAppFn.isConstOf ``Nat.Partrec do
    throwError "expected a Nat.Partrec proof"
  let f ← instantiateMVars proofType.getAppArgs.back!
  if f.hasMVar then throwError "input partial function has unresolved metavariables"
  let expected := mkApp (mkConst ``Witness) f
  let result ← reifyPartialProof e 500
  unless ← isDefEq (← inferType result) expected do
    throwError "reified partial witness does not target the input function"
  return result

def successorWitness : TotalWitness Nat.succ := total_code_from% Nat.Primrec.succ
def additionWitness : TotalWitness (Nat.unpaired (· + ·)) := total_code_from% Nat.Primrec.add
def partialAdditionWitness : Witness (↑(Nat.unpaired (· + ·))) :=
  partial_code_from% (Nat.Partrec.of_primrec Nat.Primrec.add)
def bottomWitness : Witness (fun _ : Nat => Part.none) := partial_code_from% Nat.Partrec.none

theorem bottomWitness_sound (n : Nat) : bottomWitness.code.eval n = Part.none :=
  congrFun bottomWitness.sound n

#eval additionWitness.code.evaln 10000 (Nat.pair 2 3)
#eval partialAdditionWitness.code.evaln 10000 (Nat.pair 2 3)
#eval bottomWitness.code.evaln 100 0
#print axioms additionWitness
