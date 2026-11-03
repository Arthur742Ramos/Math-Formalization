/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module
public import LambdaTuring.WeakCBVCPS
public meta import LambdaTuring.WeakCBVCPS
@[expose] public section

namespace LambdaTuring

/-- One-hole de Bruijn contexts, including binders and either application side. -/
inductive LambdaContext where
  | hole : LambdaContext
  | abs : LambdaContext → LambdaContext
  | appLeft : LambdaContext → Term → LambdaContext
  | appRight : Term → LambdaContext → LambdaContext

def LambdaContext.plug : LambdaContext → Term → Term
  | .hole, t => t
  | .abs c, t => .abs (c.plug t)
  | .appLeft c x, t => .app (c.plug t) x
  | .appRight f c, t => .app f (c.plug t)

/-- Shift all fixed syntax in a context. The hole is left untouched; the
plugging theorem below therefore requires a closed plugged term. -/
def LambdaContext.liftFrom : Nat → LambdaContext → LambdaContext
  | _, .hole => .hole
  | d, .abs c => .abs (c.liftFrom (d + 1))
  | d, .appLeft c x => .appLeft (c.liftFrom d) (LambdaTuring.liftFrom d x)
  | d, .appRight f c => .appRight (LambdaTuring.liftFrom d f) (c.liftFrom d)

theorem LambdaContext.liftFrom_plug_closed (c : LambdaContext) (t : Term)
    (ht : Scoped 0 t) (d : Nat) :
    LambdaTuring.liftFrom d (c.plug t) = (c.liftFrom d).plug t := by
  induction c generalizing d with
  | hole => exact liftFrom_scoped t 0 d ht (Nat.zero_le _)
  | abs c ih => simp [LambdaContext.plug, LambdaContext.liftFrom, LambdaTuring.liftFrom, ih]
  | appLeft c x ih => simp [LambdaContext.plug, LambdaContext.liftFrom, LambdaTuring.liftFrom, ih]
  | appRight f c ih => simp [LambdaContext.plug, LambdaContext.liftFrom, LambdaTuring.liftFrom, ih]

/-- Translate a source one-hole context into a fixed target one-hole context.
Indices in the fixed syntax are shifted across the new continuation binders. -/
def LambdaContext.cps : LambdaContext → LambdaContext
  | .hole => .hole
  | .abs c => .abs (.appRight (.var 0) (.abs ((c.cps).liftFrom 1)))
  | .appLeft c x =>
      .abs (.appLeft ((c.cps).liftFrom 0)
        (.abs (.app (.app (.var 0) (liftBy 2 (nameToValueCPS x))) (.var 1))))
  | .appRight f c =>
      .abs (.appRight (LambdaTuring.liftFrom 0 (nameToValueCPS f))
        (.abs (.appLeft (.appRight (.var 0) (((c.cps).liftFrom 0).liftFrom 0)) (.var 1))))

theorem LambdaContext.cps_plug_closed (c : LambdaContext) (t : Term) (ht : Scoped 0 t) :
    c.cps.plug (nameToValueCPS t) = nameToValueCPS (c.plug t) := by
  have htc : Scoped 0 (nameToValueCPS t) := nameToValueCPS_scoped ht
  induction c with
  | hole => rfl
  | abs c ih =>
    simp only [LambdaContext.cps, LambdaContext.plug, nameToValueCPS]
    rw [← LambdaContext.liftFrom_plug_closed _ _ htc, ih]
  | appLeft c x ih =>
    simp only [LambdaContext.cps, LambdaContext.plug, nameToValueCPS]
    rw [← LambdaContext.liftFrom_plug_closed _ _ htc, ih]
  | appRight f c ih =>
    simp only [LambdaContext.cps, LambdaContext.plug, nameToValueCPS, liftBy]
    rw [← LambdaContext.liftFrom_plug_closed _ _ htc,
      ← LambdaContext.liftFrom_plug_closed _ _ htc, ih]

/-- Closed terms are interchangeable in the hole as far as scoping is
concerned, even when the context itself contains binders. -/
theorem LambdaContext.plug_scoped_iff_of_closed (c : LambdaContext) (t u : Term)
    (ht : Scoped 0 t) (hu : Scoped 0 u) (d : Nat) :
    Scoped d (c.plug t) ↔ Scoped d (c.plug u) := by
  induction c generalizing d with
  | hole =>
    exact ⟨fun _ => scoped_mono hu (Nat.zero_le _), fun _ => scoped_mono ht (Nat.zero_le _)⟩
  | abs c ih => exact ih (d + 1)
  | appLeft c x ih => exact and_congr (ih d) Iff.rfl
  | appRight f c ih => exact and_congr Iff.rfl (ih d)

/-- The closed-hole requirement is necessary for this literal context
translation: leaving an open hole unshifted can capture its variable. -/
theorem cps_context_open_hole_counterexample :
    (LambdaContext.appRight (.var 0) .hole).cps.plug (nameToValueCPS (.var 0)) ≠
      nameToValueCPS ((LambdaContext.appRight (.var 0) .hole).plug (.var 0)) := by
  decide

/-- Fixed syntax in a context may be open in isolation and bound by an outer
context constructor; a closed plugged term remains closed in this example. -/
theorem bound_fixed_context_closed (t : Term) (ht : Scoped 0 t) :
    Scoped 0 ((LambdaContext.abs (.appRight (.var 0) .hole)).plug t) := by
  change Scoped 1 (.app (.var 0) t)
  exact ⟨by simp [Scoped], scoped_mono ht (by omega)⟩

def WeakNameConverges (t : Term) : Prop :=
  ∃ body, Relation.ReflTransGen HeadContract t (.abs body)

def WeakValueCPSConverges (t : Term) : Prop :=
  ∃ v, WeakCBVPath (.app t identityTerm) v ∧ WeakValue v

theorem LambdaContext.cps_test_closed (c : LambdaContext) (t : Term)
    (ht : Scoped 0 t) (hclosed : Scoped 0 (c.plug t)) :
    Scoped 0 (.app (c.cps.plug (nameToValueCPS t)) identityTerm) := by
  constructor
  · rw [LambdaContext.cps_plug_closed c t ht]
    exact nameToValueCPS_scoped hclosed
  · simp [identityTerm, Scoped]

/-- Every source context gives a fixed target test. The side condition asks
that the plugged source program, including the context's fixed syntax, is closed. -/
theorem LambdaContext.cps_context_adequacy (c : LambdaContext) (t : Term)
    (ht : Scoped 0 t) (hclosed : Scoped 0 (c.plug t)) :
    WeakValueCPSConverges (c.cps.plug (nameToValueCPS t)) ↔ WeakNameConverges (c.plug t) := by
  rw [LambdaContext.cps_plug_closed c t ht]
  exact valueCPS_terminates_iff_head_value (c.plug t) hclosed

/-- The same context translation also preserves the exact target-value
readback for each closed plugged source program. -/
theorem LambdaContext.cps_context_readback (c : LambdaContext) (t v : Term)
    (ht : Scoped 0 t) (hclosed : Scoped 0 (c.plug t))
    (h : WeakCBVPath (.app (c.cps.plug (nameToValueCPS t)) identityTerm) v)
    (hv : WeakValue v) :
    ∃ body, Relation.ReflTransGen HeadContract (c.plug t) (.abs body) ∧
      v = .abs (nameToValueCPS body) := by
  rw [LambdaContext.cps_plug_closed c t ht] at h
  exact valueCPS_reflect_exact hclosed h hv

/-- Source contextual equivalence for the stated one-hole context grammar,
tested only when plugging a closed term produces a closed source program. -/
def ClosedNameContextEquivalent (t u : Term) : Prop :=
  ∀ c : LambdaContext, Scoped 0 (c.plug t) →
    (WeakNameConverges (c.plug t) ↔ WeakNameConverges (c.plug u))

/-- Target equivalence only under the image of that source-context translation,
with the fixed identity continuation. -/
def ClosedTranslatedContextEquivalent (t u : Term) : Prop :=
  ∀ c : LambdaContext, Scoped 0 (c.plug t) →
    (WeakValueCPSConverges (c.cps.plug (nameToValueCPS t)) ↔
      WeakValueCPSConverges (c.cps.plug (nameToValueCPS u)))

theorem closed_context_equivalence_transport {t u : Term} (ht : Scoped 0 t) (hu : Scoped 0 u) :
    ClosedNameContextEquivalent t u ↔ ClosedTranslatedContextEquivalent t u := by
  constructor
  · intro h c hc
    have hcu := (LambdaContext.plug_scoped_iff_of_closed c t u ht hu 0).1 hc
    exact (LambdaContext.cps_context_adequacy c t ht hc).trans
      ((h c hc).trans (LambdaContext.cps_context_adequacy c u hu hcu).symm)
  · intro h c hc
    have hcu := (LambdaContext.plug_scoped_iff_of_closed c t u ht hu 0).1 hc
    exact (LambdaContext.cps_context_adequacy c t ht hc).symm.trans
      ((h c hc).trans (LambdaContext.cps_context_adequacy c u hu hcu))

#print axioms LambdaContext.cps_plug_closed
#print axioms LambdaContext.plug_scoped_iff_of_closed
#print axioms cps_context_open_hole_counterexample
#print axioms LambdaContext.cps_test_closed
#print axioms LambdaContext.cps_context_adequacy
#print axioms LambdaContext.cps_context_readback
#print axioms closed_context_equivalence_transport
end LambdaTuring
