/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Basic
public meta import LambdaTuring.Basic
public import LambdaTuring.Upstream.Confluence
public meta import LambdaTuring.Upstream.Confluence

@[expose] public section

namespace LambdaTuring



def toUpstream : Term → Cslib.LambdaCalculus.Unscoped.Untyped.Term
  | .var i => .var i
  | .abs t => .abs (toUpstream t)
  | .app a b => .app (toUpstream a) (toUpstream b)

def fromUpstream : Cslib.LambdaCalculus.Unscoped.Untyped.Term → Term
  | .var i => .var i
  | .abs t => .abs (fromUpstream t)
  | .app a b => .app (fromUpstream a) (fromUpstream b)

theorem from_to (t : Term) : fromUpstream (toUpstream t) = t := by
  induction t <;> simp_all [toUpstream, fromUpstream]

theorem to_from (t : Cslib.LambdaCalculus.Unscoped.Untyped.Term) : toUpstream (fromUpstream t) = t := by
  induction t <;> simp_all [toUpstream, fromUpstream]

theorem to_injective : Function.Injective toUpstream := by
  intro a b h
  have := congrArg fromUpstream h
  simpa [from_to] using this

theorem to_liftFrom (l : Nat) (t : Term) :
    toUpstream (liftFrom l t) = Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre 1 l (toUpstream t) := by
  induction t generalizing l with
  | var i =>
    simp only [liftFrom, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre]
    split <;> split <;> simp_all; all_goals omega
  | abs t ih => simp [liftFrom, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre, ih]
  | app a b ia ib => simp [liftFrom, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre, ia, ib]

theorem to_liftBy (n : Nat) (t : Term) :
    toUpstream (liftBy n t) = Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre n 0 (toUpstream t) := by
  induction n with
  | zero => simp [liftBy, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_rfl]
  | succ n ih =>
    simp only [liftBy, to_liftFrom, ih,
      Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_same_bound_elim, Nat.one_add]

theorem to_substAt (depth : Nat) (v t : Term) :
    toUpstream (substAt depth v t) =
      Cslib.LambdaCalculus.Unscoped.Untyped.Term.sub (toUpstream t) depth (Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre depth 0 (toUpstream v)) := by
  induction t generalizing depth with
  | var i =>
    by_cases he : i = depth
    · subst i
      simp [substAt, toUpstream, to_liftBy]
    · by_cases hlt : i < depth
      · have hnot : ¬ depth < i := by omega
        simp [substAt, he, hnot, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.var_lt_sub hlt]
      · have hgt : depth < i := by omega
        simp [substAt, he, hgt, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.var_gt_sub hgt]
  | abs t ih =>
    simp only [substAt, toUpstream, Cslib.LambdaCalculus.Unscoped.Untyped.Term.abs_sub_zero, ih, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_same_bound_elim]
    congr 3; all_goals omega
  | app a b ia ib =>
    simp only [substAt, toUpstream, ia, ib, Cslib.LambdaCalculus.Unscoped.Untyped.Term.sub, Cslib.LambdaCalculus.Unscoped.Untyped.Term.subst, Cslib.LambdaCalculus.Unscoped.Untyped.Term.decre]




theorem from_sub_zero (t s : Cslib.LambdaCalculus.Unscoped.Untyped.Term) :
    fromUpstream (Cslib.LambdaCalculus.Unscoped.Untyped.Term.sub t 0 s) =
      substAt 0 (fromUpstream s) (fromUpstream t) := by
  apply to_injective
  simp [to_substAt, to_from]

theorem beta_to_upstream {a b : Term} (h : Beta a b) :
    Cslib.LambdaCalculus.Unscoped.Untyped.Beta (toUpstream a) (toUpstream b) := by
  induction h with
  | contract body value =>
    simpa [toUpstream, to_substAt] using
      Cslib.LambdaCalculus.Unscoped.Untyped.Beta.red (toUpstream body) (toUpstream value)
  | abs _ ih => exact .abs ih
  | appLeft _ ih => exact .appL ih
  | appRight _ ih => exact .appR ih

theorem beta_from_upstream {a b : Cslib.LambdaCalculus.Unscoped.Untyped.Term}
    (h : Cslib.LambdaCalculus.Unscoped.Untyped.Beta a b) :
    Beta (fromUpstream a) (fromUpstream b) := by
  induction h with
  | red body value =>
    simpa [fromUpstream, from_sub_zero] using Beta.contract (fromUpstream body) (fromUpstream value)
  | abs _ ih => exact .abs ih
  | appL _ ih => exact .appLeft ih
  | appR _ ih => exact .appRight ih

theorem reaches_to_upstream {a b : Term} (h : Reaches a b) :
    Relation.ReflTransGen Cslib.LambdaCalculus.Unscoped.Untyped.Beta
      (toUpstream a) (toUpstream b) := by
  induction h with
  | refl => exact .refl
  | step h _ ih => exact .head (beta_to_upstream h) ih

theorem reaches_from_upstream {a b : Cslib.LambdaCalculus.Unscoped.Untyped.Term}
    (h : Relation.ReflTransGen Cslib.LambdaCalculus.Unscoped.Untyped.Beta a b) :
    Reaches (fromUpstream a) (fromUpstream b) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head h _ ih => exact .step (beta_from_upstream h) ih

/-- Full compatible beta reduction is confluent on all untyped terms. -/
theorem beta_confluent {a b c : Term} (hab : Reaches a b) (hac : Reaches a c) :
    ∃ d, Reaches b d ∧ Reaches c d := by
  obtain ⟨d, hbd, hcd⟩ :=
    Cslib.LambdaCalculus.Unscoped.Untyped.churchRosser_beta
      (reaches_to_upstream hab) (reaches_to_upstream hac)
  refine ⟨fromUpstream d, ?_, ?_⟩
  · simpa only [from_to] using reaches_from_upstream hbd
  · simpa only [from_to] using reaches_from_upstream hcd

/-- Any two reachable Church numeral results have the same index. -/
theorem numeral_result_unique {t : Term} {m n : Nat}
    (hm : Reaches t (church m)) (hn : Reaches t (church n)) : m = n := by
  obtain ⟨d, hmd, hnd⟩ := beta_confluent hm hn
  have hm' := normal_reaches_eq (church_no_beta m) hmd
  have hn' := normal_reaches_eq (church_no_beta n) hnd
  exact church_injective (hm'.trans hn'.symm)

#print axioms to_substAt
#print axioms beta_confluent
#print axioms numeral_result_unique
end LambdaTuring
