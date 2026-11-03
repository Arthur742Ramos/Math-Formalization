/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.HeadObservable
public meta import LambdaTuring.HeadObservable

@[expose] public section

/- Standard reduction adapts Isabelle/HOL's HOL-Proofs-Lambda.Standardization:
   Author Stefan Berghofer, Copyright 2005 TU Muenchen. It follows Ralph
   Matthes' notes and Loader's proof idea. The Isabelle distribution's BSD
   notice and disclaimer are retained in THIRD_PARTY_NOTICES.md. -/

namespace LambdaTuring

/-- Application of a term to a list of arguments, from left to right. -/
def applySpine (t : Term) : List Term → Term
  | [] => t
  | x :: xs => applySpine (.app t x) xs

@[simp] theorem applySpine_nil (t : Term) : applySpine t [] = t := rfl
@[simp] theorem applySpine_cons (t x : Term) (xs : List Term) :
    applySpine t (x :: xs) = applySpine (.app t x) xs := rfl

theorem applySpine_append (t : Term) (xs ys : List Term) :
    applySpine t (xs ++ ys) = applySpine (applySpine t xs) ys := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => exact ih (.app t x)

theorem liftFrom_applySpine (t : Term) (xs : List Term) (depth : Nat) :
    liftFrom depth (applySpine t xs) = applySpine (liftFrom depth t) (xs.map (liftFrom depth)) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simpa [applySpine, liftFrom] using ih (.app t x)

theorem substAt_applySpine (t : Term) (xs : List Term) (depth : Nat) (value : Term) :
    substAt depth value (applySpine t xs) =
      applySpine (substAt depth value t) (xs.map (substAt depth value)) := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => simpa [applySpine, substAt] using ih (.app t x)

theorem headContract_applySpine {t u : Term} (h : HeadContract t u) (xs : List Term) :
    HeadContract (applySpine t xs) (applySpine u xs) := by
  induction xs generalizing t u with
  | nil => exact h
  | cons x xs ih => exact ih (.appLeft x h)

mutual
  /-- Standard reduction contracts a head redex before its residual work. -/
  inductive StandardReduction : Term → Term → Prop where
    | var (n : Nat) {xs ys : List Term} : StandardReductionList xs ys →
        StandardReduction (applySpine (.var n) xs) (applySpine (.var n) ys)
    | abs {body body' : Term} {xs ys : List Term} : StandardReduction body body' →
        StandardReductionList xs ys →
        StandardReduction (applySpine (.abs body) xs) (applySpine (.abs body') ys)
    | head {body arg target : Term} {xs : List Term} :
        StandardReduction (applySpine (substAt 0 arg body) xs) target →
        StandardReduction (applySpine (.app (.abs body) arg) xs) target

  inductive StandardReductionList : List Term → List Term → Prop where
    | nil : StandardReductionList [] []
    | cons {x y : Term} {xs ys : List Term} : StandardReduction x y →
        StandardReductionList xs ys → StandardReductionList (x :: xs) (y :: ys)
end

theorem standardList_refl_of {xs : List Term} (h : ∀ x ∈ xs, StandardReduction x x) :
    StandardReductionList xs xs := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    apply StandardReductionList.cons (h x (by simp))
    exact ih (by intro y hy; exact h y (by simp [hy]))

theorem standardReduction_refl (t : Term) : StandardReduction t t := by
  have h : ∀ t : Term, ∀ xs, (∀ x ∈ xs, StandardReduction x x) →
      StandardReduction (applySpine t xs) (applySpine t xs) := by
    intro t
    induction t with
    | var n =>
      intro xs hx
      exact .var n (standardList_refl_of hx)
    | abs body ih =>
      intro xs hx
      exact .abs (ih [] (by simp)) (standardList_refl_of hx)
    | app f x ihf ihx =>
      intro xs hx
      apply ihf (x :: xs)
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ihx [] (by simp)
      · exact hx y hy
  exact h t [] (by simp)

theorem standardList_append {xs ys xs' ys' : List Term}
    (h : StandardReductionList xs ys) (h' : StandardReductionList xs' ys') :
    StandardReductionList (xs ++ xs') (ys ++ ys') := by
  induction h using StandardReductionList.rec (motive_1 := fun _ _ _ => True) with
  | nil => exact h'
  | cons hx _ _ ih => exact .cons hx ih
  | var => trivial
  | abs => trivial
  | head => trivial

theorem standardReduction_app {t u x y : Term}
    (h : StandardReduction t u) (hxy : StandardReduction x y) :
    StandardReduction (.app t x) (.app u y) := by
  induction h using StandardReduction.rec (motive_2 := fun _ _ _ => True) with
  | var n hs _ =>
    have hl := standardList_append hs (.cons hxy .nil)
    simpa [applySpine_append] using StandardReduction.var n hl
  | abs hb hs _ _ =>
    have hl := standardList_append hs (.cons hxy .nil)
    simpa [applySpine_append] using StandardReduction.abs hb hl
  | head h ih =>
    have hh := StandardReduction.head (xs := _ ++ [x]) (by simpa [applySpine_append] using ih)
    simpa [applySpine_append] using hh
  | nil => trivial
  | cons => trivial

theorem beta_standardReduction {t u : Term} (h : Beta t u) : StandardReduction t u := by
  induction h with
  | contract body arg =>
    exact StandardReduction.head (xs := []) (standardReduction_refl _)
  | abs _ ih => exact StandardReduction.abs (xs := []) (ys := []) ih .nil
  | appLeft _ ih => exact standardReduction_app ih (standardReduction_refl _)
  | appRight _ ih => exact standardReduction_app (standardReduction_refl _) ih

theorem reaches_applySpine {f g : Term} (h : Reaches f g) {xs ys : List Term}
    (hs : List.Forall₂ Reaches xs ys) : Reaches (applySpine f xs) (applySpine g ys) := by
  induction hs generalizing f g with
  | nil => exact h
  | cons hx _ ih => exact ih (reaches_app_both h hx)

theorem standardReduction_reaches {t u : Term} (h : StandardReduction t u) : Reaches t u := by
  induction h using StandardReduction.rec
      (motive_2 := fun xs ys _ => List.Forall₂ Reaches xs ys) with
  | var n _ ih => exact reaches_applySpine (.refl (.var n)) ih
  | abs _ _ ih ihs => exact reaches_applySpine (reaches_abs ih) ihs
  | head _ ih => exact .step (headContract_beta (headContract_applySpine (.root _ _) _)) ih
  | nil => exact .nil
  | cons _ _ ih ihs => exact .cons ih ihs

theorem standardReduction_liftFrom {t u : Term} (h : StandardReduction t u) (depth : Nat) :
    StandardReduction (liftFrom depth t) (liftFrom depth u) := by
  induction h using StandardReduction.rec
      (motive_2 := fun xs ys _ => ∀ d, StandardReductionList (xs.map (liftFrom d)) (ys.map (liftFrom d)))
      generalizing depth with
  | var n hs ih =>
    rw [liftFrom_applySpine, liftFrom_applySpine]
    by_cases hn : n < depth
    · simpa [liftFrom, hn] using StandardReduction.var n (ih depth)
    · simpa [liftFrom, hn] using StandardReduction.var (n + 1) (ih depth)
  | abs hb hs ih ihs =>
    rw [liftFrom_applySpine, liftFrom_applySpine]
    exact StandardReduction.abs (ih (depth + 1)) (ihs depth)
  | head hb ih =>
    rw [liftFrom_applySpine]
    apply StandardReduction.head
    simpa [liftFrom_applySpine, liftFrom_contract_comm] using ih depth
  | nil d => exact .nil
  | cons hx hs ih ihs d => exact .cons (ih d) (ihs d)

theorem standardReduction_liftBy {t u : Term} (h : StandardReduction t u) (n : Nat) :
    StandardReduction (liftBy n t) (liftBy n u) := by
  induction n with
  | zero => exact h
  | succ n ih => exact standardReduction_liftFrom ih 0

theorem standardReduction_applySpine {t u : Term} (h : StandardReduction t u)
    {xs ys : List Term} (hs : StandardReductionList xs ys) :
    StandardReduction (applySpine t xs) (applySpine u ys) := by
  induction hs using StandardReductionList.rec (motive_1 := fun _ _ _ => True) generalizing t u with
  | nil => exact h
  | cons hx hs _ ih => exact ih (standardReduction_app h hx)
  | var => trivial
  | abs => trivial
  | head => trivial

theorem standardReduction_subst {t u value value' : Term} (h : StandardReduction t u)
    (hv : StandardReduction value value') (depth : Nat) :
    StandardReduction (substAt depth value t) (substAt depth value' u) := by
  induction h using StandardReduction.rec
      (motive_2 := fun xs ys _ => ∀ d v v', StandardReduction v v' →
        StandardReductionList (xs.map (substAt d v)) (ys.map (substAt d v')))
      generalizing depth value value' with
  | var n hs ih =>
    rw [substAt_applySpine, substAt_applySpine]
    apply standardReduction_applySpine _ (ih depth value value' hv)
    by_cases he : n = depth
    · subst n
      simpa [substAt] using standardReduction_liftBy hv depth
    · by_cases hl : depth < n
      · simpa [substAt, he, hl] using standardReduction_refl (.var (n - 1))
      · simpa [substAt, he, hl] using standardReduction_refl (.var n)
  | abs hb hs ih ihs =>
    rw [substAt_applySpine, substAt_applySpine]
    exact StandardReduction.abs (ih hv (depth + 1)) (ihs depth value value' hv)
  | head hb ih =>
    rw [substAt_applySpine]
    apply StandardReduction.head
    simpa [substAt_applySpine, substAt_contract_comm] using ih hv depth
  | nil d v v' hv => exact .nil
  | cons hx hs ih ihs d v v' hv => exact .cons (ih hv d) (ihs d v v' hv)

/-- One beta step in exactly one argument of a spine. -/
inductive SpineListBeta : List Term → List Term → Prop where
  | head {x y : Term} {xs : List Term} : Beta x y → SpineListBeta (x :: xs) (y :: xs)
  | tail (x : Term) {xs ys : List Term} : SpineListBeta xs ys → SpineListBeta (x :: xs) (x :: ys)

/-- A beta step in an application spine lies in the head, in an argument,
    or contracts the head abstraction against its first argument. -/
theorem beta_applySpine_cases (t : Term) (xs : List Term) {u : Term}
    (h : Beta (applySpine t xs) u) :
    (∃ t', Beta t t' ∧ u = applySpine t' xs) ∨
    (∃ ys, SpineListBeta xs ys ∧ u = applySpine t ys) ∨
    (∃ body arg rest, t = .abs body ∧ xs = arg :: rest ∧
      u = applySpine (substAt 0 arg body) rest) := by
  induction xs generalizing t u with
  | nil => exact Or.inl ⟨u, h, rfl⟩
  | cons x xs ih =>
    rcases ih (.app t x) h with ⟨q, hq, rfl⟩ | ⟨ys, hys, rfl⟩ | ⟨body, arg, rest, heq, _, _⟩
    · cases hq with
      | contract body arg => exact Or.inr (Or.inr ⟨body, _, xs, rfl, rfl, rfl⟩)
      | appLeft hb => exact Or.inl ⟨_, hb, rfl⟩
      | appRight hb => exact Or.inr (Or.inl ⟨_ :: xs, .head hb, rfl⟩)
    · exact Or.inr (Or.inl ⟨x :: ys, .tail x hys, rfl⟩)
    · cases heq

/-- Standard reduction is stable under one further full-beta step. -/
theorem standardReduction_beta_tail {t u v : Term} (h : StandardReduction t u) (hb : Beta u v) :
    StandardReduction t v := by
  induction h using StandardReduction.rec
      (motive_2 := fun xs ys _ => ∀ zs, SpineListBeta ys zs → StandardReductionList xs zs)
      generalizing v with
  | @var n xs ys hs ih =>
    rcases beta_applySpine_cases (.var n) ys hb with ⟨q, hq, heq⟩ | ⟨zs, hzs, heq⟩ | ⟨body, arg, rest, heq, _, _⟩
    · cases hq
    · subst v
      exact .var n (ih zs hzs)
    · cases heq
  | @abs body body' xs ys hbdy hs ihbody ihs =>
    rcases beta_applySpine_cases (.abs body') ys hb with ⟨q, hq, heq⟩ | ⟨zs, hzs, heq⟩ | ⟨body'', arg, rest, heq, hys, hv⟩
    · subst v
      cases hq with
      | abs hq => exact .abs (ihbody hq) hs
    · subst v
      exact .abs hbdy (ihs zs hzs)
    · cases heq
      subst ys
      subst v
      cases hs with
      | cons harg htail =>
        exact .head (standardReduction_applySpine (standardReduction_subst hbdy harg 0) htail)
  | head hs ih => exact .head (ih hb)
  | nil zs h => cases h
  | cons hx hs ih ihs zs h =>
    cases h with
    | head hb => exact .cons (ih hb) hs
    | tail _ hb => exact .cons hx (ihs _ hb)

/-- Standardization of arbitrary finite full-beta reductions. -/
theorem reaches_standardReduction {t u : Term} (h : Reaches t u) : StandardReduction t u := by
  have hstar : Relation.ReflTransGen Beta t u := by
    induction h with
    | refl => exact .refl
    | step h _ ih => exact .head h ih
  clear h
  induction hstar with
  | refl => exact standardReduction_refl _
  | tail _ h ih => exact standardReduction_beta_tail ih h

/-- The leftmost head of an application spine. -/
def spineHead : Term → Term
  | .app f _ => spineHead f
  | t => t

def spineArguments : Term → List Term
  | .app f x => spineArguments f ++ [x]
  | _ => []

theorem spineHead_applySpine (t : Term) (xs : List Term) :
    spineHead (applySpine t xs) = spineHead t := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => exact ih (.app t x)

theorem spineArguments_applySpine (t : Term) (xs : List Term) :
    spineArguments (applySpine t xs) = spineArguments t ++ xs := by
  induction xs generalizing t with
  | nil => simp
  | cons x xs ih => simpa [spineArguments, List.append_assoc] using ih (.app t x)

theorem standardList_reaches {xs ys : List Term} (h : StandardReductionList xs ys) :
    List.Forall₂ Reaches xs ys := by
  induction h using StandardReductionList.rec (motive_1 := fun _ _ _ => True) with
  | nil => exact .nil
  | cons hx hs _ ih => exact .cons (standardReduction_reaches hx) ih
  | var => trivial
  | abs => trivial
  | head => trivial

/-- A standard reduction to a variable-headed term first reduces the source
    head to that variable and then reduces its individual arguments. -/
theorem standardReduction_variable_prefix {t u : Term} (h : StandardReduction t u) :
    ∀ x ys, u = applySpine (.var x) ys →
      ∃ xs, Relation.ReflTransGen HeadContract t (applySpine (.var x) xs) ∧ StandardReductionList xs ys := by
  induction h using StandardReduction.rec (motive_2 := fun _ _ _ => True) with
  | @var n xs zs hs _ =>
    intro x ys heq
    have hn : n = x := by
      have hhead := congrArg spineHead heq
      simpa [spineHead_applySpine, spineHead] using hhead
    have hzs : zs = ys := by
      have hargs := congrArg spineArguments heq
      simpa [spineArguments_applySpine, spineArguments] using hargs
    subst n
    subst zs
    exact ⟨xs, .refl, hs⟩
  | @abs body body' xs zs hb hs _ _ =>
    intro x ys heq
    have hhead := congrArg spineHead heq
    simp [spineHead_applySpine, spineHead] at hhead
  | @head body arg target xs hs ih =>
    intro x ys heq
    obtain ⟨ws, hhead, hargs⟩ := ih x ys heq
    exact ⟨ws, .head (headContract_applySpine (.root body arg) xs) hhead, hargs⟩
  | nil => trivial
  | cons => trivial

theorem variableHeadStandardization_proved : VariableHeadStandardization := by
  intro t x h
  obtain ⟨xs, hp, hs⟩ := standardReduction_variable_prefix (reaches_standardReduction h) x [] rfl
  cases hs with
  | nil => exact hp

theorem variableApplicationHeadPrefix_proved : VariableApplicationHeadPrefix := by
  intro t x n h
  obtain ⟨xs, hp, hs⟩ := standardReduction_variable_prefix (reaches_standardReduction h) x [church n] rfl
  cases hs with
  | cons hW htail =>
    cases htail with
    | nil => exact ⟨_, hp, standardReduction_reaches hW⟩

theorem headContract_has_abs_head {t u : Term} (h : HeadContract t u) :
    ∃ body, spineHead t = .abs body := by
  induction h with
  | root body arg => exact ⟨body, rfl⟩
  | appLeft x _ ih => exact ih

theorem variableSpine_no_head (n : Nat) (xs : List Term) :
    ¬ ∃ u, HeadContract (applySpine (.var n) xs) u := by
  rintro ⟨u, hu⟩
  obtain ⟨body, hb⟩ := headContract_has_abs_head hu
  simp [spineHead_applySpine, spineHead] at hb

/-- A standard reduction to a beta-normal form gives accessibility of the
    source under head contraction. -/
theorem standardReduction_headAccessible_of_normal {t u : Term} (h : StandardReduction t u) :
    (¬ ∃ v, Beta u v) → HeadAccessible t := by
  induction h using StandardReduction.rec (motive_2 := fun _ _ _ => True) with
  | var n hs _ =>
    intro hn
    exact headAccessible_of_no_head (variableSpine_no_head n _)
  | @abs body body' xs ys hb hs ih ihs =>
    intro hn
    cases ys with
    | nil =>
      cases hs with
      | nil => exact headAccessible_of_no_head (by rintro ⟨v, hv⟩; exact headContract_abs_impossible hv)
    | cons arg rest =>
      have hhead := headContract_applySpine (HeadContract.root body' arg) rest
      exact False.elim (hn ⟨_, headContract_beta hhead⟩)
  | @head body arg target xs hs ih =>
    intro hn
    exact headAccessible_backward (headContract_applySpine (.root body arg) xs) (ih hn)
  | nil => trivial
  | cons => trivial

theorem weakNormalizationImpliesHeadAccessible_proved : WeakNormalizationImpliesHeadAccessible := by
  intro t hn
  obtain ⟨N, h, normal⟩ := hn
  exact standardReduction_headAccessible_of_normal (reaches_standardReduction h) normal

theorem headStandardizationObligations_proved : HeadStandardizationObligations :=
  ⟨variableHeadStandardization_proved, variableApplicationHeadPrefix_proved,
    weakNormalizationImpliesHeadAccessible_proved⟩

/-- Unconditional strict CPS compilation of Mathlib's minimization case. -/
theorem cpsMinimize_code {G : Term} {f : Nat.Partrec.Code}
    (hg : CPSRepresents G (Nat.Partrec.Code.eval f)) :
    CPSRepresents (cpsMinimize G) (Nat.Partrec.Code.eval (.rfind' f)) :=
  cpsMinimize_code_of_head_standardization hg headStandardizationObligations_proved

#print axioms standardReduction_refl
#print axioms standardReduction_app
#print axioms beta_standardReduction
#print axioms standardReduction_reaches
#print axioms standardReduction_liftFrom
#print axioms standardReduction_subst
#print axioms beta_applySpine_cases
#print axioms standardReduction_beta_tail
#print axioms reaches_standardReduction
#print axioms variableHeadStandardization_proved
#print axioms variableApplicationHeadPrefix_proved
#print axioms weakNormalizationImpliesHeadAccessible_proved
#print axioms cpsMinimize_code

end LambdaTuring
