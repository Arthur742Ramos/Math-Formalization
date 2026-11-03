/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.HeadSearch
public meta import LambdaTuring.HeadSearch

@[expose] public section

/- The head-substitution transport follows the related Isabelle
   Lambda_Head_Standardization proof, using the adapted CSLib substitution law. -/

namespace LambdaTuring

/-- The root contraction commutes with an enclosing substitution. -/
theorem substAt_contract_comm (body arg value : Term) (depth : Nat) :
    substAt depth value (substAt 0 arg body) =
      substAt 0 (substAt depth value arg) (substAt (depth + 1) value body) := by
  apply to_injective
  simp only [to_substAt, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_rfl]
  simpa [Nat.add_comm] using
    (Cslib.LambdaCalculus.Unscoped.Untyped.Term.sub_sub_incre
      (t := toUpstream body) (s := toUpstream arg) (u := toUpstream value)
      (n := depth) (k := depth)).symm

/-- Head contractions survive capture-avoiding substitution. -/
theorem headContract_subst {t u : Term} (h : HeadContract t u) (depth : Nat) (value : Term) :
    HeadContract (substAt depth value t) (substAt depth value u) := by
  induction h with
  | root body arg =>
    simp only [substAt]
    rw [substAt_contract_comm body arg value depth]
    exact .root _ _
  | appLeft x _ ih =>
    simp only [substAt]
    exact .appLeft _ ih

theorem headBlock_subst {t u : Term} (h : Relation.TransGen HeadContract t u)
    (depth : Nat) (value : Term) :
    Relation.TransGen HeadContract (substAt depth value t) (substAt depth value u) := by
  induction h with
  | single h => exact .single (headContract_subst h depth value)
  | tail _ h ih => exact .tail ih (headContract_subst h depth value)

theorem headStar_subst {t u : Term} (h : Relation.ReflTransGen HeadContract t u)
    (depth : Nat) (value : Term) :
    Relation.ReflTransGen HeadContract (substAt depth value t) (substAt depth value u) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact .tail ih (headContract_subst h depth value)

theorem headBlock_reaches {t u : Term} (h : Relation.TransGen HeadContract t u) : Reaches t u := by
  induction h with
  | single h => exact .step (headContract_beta h) (.refl _)
  | tail _ h ih => exact reaches_trans ih (.step (headContract_beta h) (.refl _))

/-- Lifting also commutes with root contraction. -/
theorem liftFrom_contract_comm (body arg : Term) (depth : Nat) :
    liftFrom depth (substAt 0 arg body) =
      substAt 0 (liftFrom depth arg) (liftFrom (depth + 1) body) := by
  apply to_injective
  simp only [to_liftFrom, to_substAt, Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_rfl]
  simpa using
    (Cslib.LambdaCalculus.Unscoped.Untyped.Term.incre_sub
      (i := 1) (l := depth) (n := 0) (t := toUpstream body) (s := toUpstream arg)).symm

theorem beta_subst {t u : Term} (h : Beta t u) (depth : Nat) (value : Term) :
    Beta (substAt depth value t) (substAt depth value u) := by
  induction h generalizing depth with
  | contract body arg =>
    simp only [substAt]
    rw [substAt_contract_comm body arg value depth]
    exact .contract _ _
  | abs h ih =>
    simp only [substAt]
    exact .abs (ih (depth + 1))
  | appLeft h ih =>
    simp only [substAt]
    exact .appLeft (ih depth)
  | appRight h ih =>
    simp only [substAt]
    exact .appRight (ih depth)

theorem reaches_subst {t u : Term} (h : Reaches t u) (depth : Nat) (value : Term) :
    Reaches (substAt depth value t) (substAt depth value u) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (beta_subst h depth value) ih

theorem beta_liftFrom {t u : Term} (h : Beta t u) (depth : Nat) :
    Beta (liftFrom depth t) (liftFrom depth u) := by
  induction h generalizing depth with
  | contract body arg =>
    simp only [liftFrom]
    rw [liftFrom_contract_comm body arg depth]
    exact .contract _ _
  | abs h ih =>
    simp only [liftFrom]
    exact .abs (ih (depth + 1))
  | appLeft h ih =>
    simp only [liftFrom]
    exact .appLeft (ih depth)
  | appRight h ih =>
    simp only [liftFrom]
    exact .appRight (ih depth)

theorem reaches_liftFrom {t u : Term} (h : Reaches t u) (depth : Nat) :
    Reaches (liftFrom depth t) (liftFrom depth u) := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step (beta_liftFrom h depth) ih

#print axioms substAt_contract_comm
#print axioms headBlock_subst
#print axioms reaches_subst
#print axioms reaches_liftFrom

end LambdaTuring
