/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import Lean

@[expose] public section

/-! Full beta reduction on untyped de Bruijn terms and Church numeral observations.

This is an initial component, not the lambda–Turing equivalence theorem. -/

namespace LambdaTuring

inductive Term where
  | var : Nat → Term
  | abs : Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

/-- Shift free indices at and above a cutoff by one. -/
def liftFrom (cutoff : Nat) : Term → Term
  | .var i => .var (if i < cutoff then i else i + 1)
  | .abs body => .abs (liftFrom (cutoff + 1) body)
  | .app f x => .app (liftFrom cutoff f) (liftFrom cutoff x)

/-- Shift a term repeatedly when moving it under binders. -/
def liftBy : Nat → Term → Term
  | 0, t => t
  | n + 1, t => liftFrom 0 (liftBy n t)

/-- Substitute the outermost bound variable and remove its binder. -/
def substAt (depth : Nat) (value : Term) : Term → Term
  | .var i => if i = depth then liftBy depth value
      else .var (if depth < i then i - 1 else i)
  | .abs body => .abs (substAt (depth + 1) value body)
  | .app f x => .app (substAt depth value f) (substAt depth value x)

/-- One full beta step, including reductions under lambda. -/
inductive Beta : Term → Term → Prop where
  | contract (body value : Term) : Beta (.app (.abs body) value) (substAt 0 value body)
  | abs {a b : Term} : Beta a b → Beta (.abs a) (.abs b)
  | appLeft {a b x : Term} : Beta a b → Beta (.app a x) (.app b x)
  | appRight {f a b : Term} : Beta a b → Beta (.app f a) (.app f b)

/-- Reflexive transitive closure, in execution order. -/
inductive Reaches : Term → Term → Prop where
  | refl (t : Term) : Reaches t t
  | step {a b c : Term} : Beta a b → Reaches b c → Reaches a c

/-- `f` is variable 1, `x` is variable 0. -/
def churchBody : Nat → Term
  | 0 => .var 0
  | n + 1 => .app (.var 1) (churchBody n)

def church (n : Nat) : Term := .abs (.abs (churchBody n))

theorem var_no_beta (i : Nat) : ¬ ∃ t, Beta (.var i) t := by
  rintro ⟨_, h⟩
  cases h

theorem churchBody_no_beta (n : Nat) : ¬ ∃ t, Beta (churchBody n) t := by
  induction n with
  | zero => exact var_no_beta 0
  | succ n ih =>
    rintro ⟨_, h⟩
    cases h with
    | appLeft h => cases h
    | appRight h => exact ih ⟨_, h⟩

theorem church_no_beta (n : Nat) : ¬ ∃ t, Beta (church n) t := by
  rintro ⟨_, h⟩
  cases h with
  | abs h =>
    cases h with
    | abs h => exact churchBody_no_beta n ⟨_, h⟩

theorem normal_reaches_eq {a b : Term} (h : ¬ ∃ t, Beta a t) (r : Reaches a b) : a = b := by
  cases r with
  | refl => rfl
  | step s _ => exact False.elim (h ⟨_, s⟩)

theorem churchBody_injective : Function.Injective churchBody := by
  intro m n h
  induction m generalizing n with
  | zero => cases n <;> simp_all [churchBody]
  | succ m ih =>
    cases n with
    | zero => simp [churchBody] at h
    | succ n =>
      have eqbody : churchBody m = churchBody n := by
        simpa only [churchBody, Term.app.injEq, true_and] using h
      exact congrArg Nat.succ (ih eqbody)

theorem church_injective : Function.Injective church := by
  intro m n h
  apply churchBody_injective
  simpa only [church, Term.abs.injEq] using h

theorem church_reaches_church_iff (m n : Nat) : Reaches (church m) (church n) ↔ m = n := by
  constructor
  · intro h
    exact church_injective (normal_reaches_eq (church_no_beta m) h)
  · intro h
    subst n
    exact .refl _

end LambdaTuring

namespace LambdaTuring

/-- Every variable in the term is bound within the given number of binders. -/
def Scoped (depth : Nat) : Term → Prop
  | .var i => i < depth
  | .abs body => Scoped (depth + 1) body
  | .app f x => Scoped depth f ∧ Scoped depth x

theorem churchBody_scoped (n : Nat) : Scoped 2 (churchBody n) := by
  induction n with
  | zero => simp [churchBody, Scoped]
  | succ n ih => simpa [churchBody, Scoped] using ih

theorem church_closed (n : Nat) : Scoped 0 (church n) := churchBody_scoped n

-- Capture-avoidance and removal of the discharged binder are part of the
-- operational definition, including reduction under an enclosing lambda.
example : substAt 0 (.var 0) (.abs (.app (.var 1) (.var 2))) =
    .abs (.app (.var 1) (.var 1)) := rfl
example : Beta (.abs (.app (.abs (.var 0)) (.var 0))) (.abs (.var 0)) := by
  exact .abs (.contract _ _)

#print axioms church_closed
#print axioms church_reaches_church_iff

end LambdaTuring
