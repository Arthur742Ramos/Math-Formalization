/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSSearch
public meta import LambdaTuring.CPSSearch

@[expose] public section

/- Head contraction and accessibility are used in the related Isabelle
   Lambda_Head_Normalization development. The bridge from weak normalization
   to head accessibility is not assumed or claimed here. -/

namespace LambdaTuring

/-- Contract the leftmost outer redex without entering arguments or binders. -/
inductive HeadContract : Term → Term → Prop where
  | root (body value : Term) : HeadContract (.app (.abs body) value) (substAt 0 value body)
  | appLeft {f f' : Term} (x : Term) : HeadContract f f' → HeadContract (.app f x) (.app f' x)

theorem headContract_beta {t u : Term} (h : HeadContract t u) : Beta t u := by
  induction h with
  | root body value => exact .contract body value
  | appLeft x _ ih => exact .appLeft ih

theorem headContract_abs_impossible {t u : Term} : ¬ HeadContract (.abs t) u := by
  intro h
  cases h

theorem headContract_deterministic {t u v : Term}
    (hu : HeadContract t u) (hv : HeadContract t v) : u = v := by
  induction hu generalizing v with
  | root body value =>
    cases hv with
    | root => rfl
    | appLeft _ h => exact False.elim (headContract_abs_impossible h)
  | appLeft x h ih =>
    cases hv with
    | root => exact False.elim (headContract_abs_impossible h)
    | appLeft _ h' => exact congrArg (fun z => Term.app z x) (ih h')

theorem headBlock_appLeft {t u : Term} (h : Relation.TransGen HeadContract t u) (x : Term) :
    Relation.TransGen HeadContract (.app t x) (.app u x) := by
  induction h with
  | single h => exact .single (.appLeft x h)
  | tail _ h ih => exact .tail ih (.appLeft x h)

theorem lambdaFix_head_unfold {F : Term} (hf : Scoped 0 F) :
    HeadContract (lambdaFix F) (.app F (lambdaFix F)) := by
  have hF := substAt_scoped F 0 (fixDelta F) hf
  have h := HeadContract.root (.app F (.app (.var 0) (.var 0))) (fixDelta F)
  simp only [substAt, hF] at h
  exact h

theorem cpsSearchLoop_head_unfold {G : Term} (hg : Scoped 0 G) (A I K : Term) :
    HeadContract (.app (.app (.app (cpsSearchLoop G) A) I) K)
      (.app (.app (.app (.app (cpsSearchBody G) (cpsSearchLoop G)) A) I) K) :=
  .appLeft K (.appLeft I (.appLeft A (lambdaFix_head_unfold (cpsSearchBody_closed hg))))

def HeadAccessible (t : Term) : Prop := Acc (fun u t => HeadContract t u) t

theorem headAccessible_of_no_head {t : Term} (hn : ¬ ∃ u, HeadContract t u) : HeadAccessible t := by
  apply Acc.intro
  intro u hu
  exact False.elim (hn ⟨u, hu⟩)

theorem headAccessible_backward {t u : Term} (h : HeadContract t u)
    (hu : HeadAccessible u) : HeadAccessible t := by
  apply Acc.intro
  intro v hv
  have heq := headContract_deterministic h hv
  subst v
  exact hu

theorem headAccessible_of_head_normalizing {t u : Term}
    (h : Relation.ReflTransGen HeadContract t u) (hn : ¬ ∃ v, HeadContract u v) : HeadAccessible t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact headAccessible_of_no_head hn
  | head h _ ih => exact headAccessible_backward h ih

/-- The inverse-oriented accessibility relation supports nonempty forward blocks. -/
theorem headBlock_reverse {t u : Term} (h : Relation.TransGen HeadContract t u) :
    Relation.TransGen (fun u t => HeadContract t u) u t := by
  induction h with
  | single h => exact .single h
  | tail _ h ih => exact .head h ih

/-- Infinitely many nonempty head blocks rule out head accessibility. -/
theorem headBlocksInfinite_not_accessible (T : Nat → Term)
    (run : ∀ n, Relation.TransGen HeadContract (T n) (T (n + 1))) : ¬ HeadAccessible (T 0) := by
  intro h
  have hgeneral : ∀ t, Acc (Relation.TransGen (fun u t => HeadContract t u)) t →
      ∀ n, t = T n → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro n heq
      have hs : Relation.TransGen (fun u t => HeadContract t u) (T (n + 1)) t := by
        simpa [heq] using headBlock_reverse (run n)
      exact ih _ hs (n + 1) rfl
  exact hgeneral (T 0) h.transGen 0 rfl

/-- A sequence of head contractions contradicts accessibility. -/
theorem headInfinite_not_accessible (T : Nat → Term)
    (run : ∀ n, HeadContract (T n) (T (n + 1))) : ¬ HeadAccessible (T 0) := by
  intro h
  have hgeneral : ∀ t, HeadAccessible t → ∀ n, t = T n → False := by
    intro t ht
    induction ht with
    | intro t _ ih =>
      intro n heq
      have hs : HeadContract t (T (n + 1)) := by simpa [heq] using run n
      exact ih _ hs (n + 1) rfl
  exact hgeneral (T 0) h 0 rfl

/-- A normal term has no head contraction. -/
theorem normal_no_head {t : Term} (hn : ¬ ∃ u, Beta t u) : ¬ ∃ u, HeadContract t u := by
  rintro ⟨u, hu⟩
  exact hn ⟨u, headContract_beta hu⟩

#print axioms headContract_deterministic
#print axioms headInfinite_not_accessible
#print axioms headBlocksInfinite_not_accessible

end LambdaTuring
