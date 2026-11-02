/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.HeadSubstitution
public meta import LambdaTuring.HeadSubstitution
public import LambdaTuring.CPSSearchExact
public meta import LambdaTuring.CPSSearchExact

@[expose] public section

/- Fresh-marker argument adapted from the related Isabelle
   Lambda_CPS_Unary_Minimization theory. The head-standardization hypothesis
   is explicit and is not asserted as a theorem. -/

namespace LambdaTuring

/-- Variable-target case of head standardization, still to be proved. -/
def VariableHeadStandardization : Prop :=
  ∀ t x, Reaches t (.var x) → Relation.ReflTransGen HeadContract t (.var x)

/-- A term that beta-reaches a positive numeral is observably positive,
    assuming the variable-target standardization lemma. -/
theorem beta_positive_observable (standardization : VariableHeadStandardization)
    {V : Term} {v : Nat} (positive : Reaches V (church (v + 1))) : HeadPositiveResult V := by
  intro A B
  let W := liftFrom 0 (liftFrom 0 V)
  let T : Term := .app (.app (.app churchIsZero W) (.var 1)) (.var 0)
  have hn : liftFrom 0 (church (v + 1)) = church (v + 1) :=
    liftFrom_scoped (church (v + 1)) 0 0 (church_closed _) (le_refl _)
  have hw : Reaches W (church (v + 1)) := by
    simpa [W, hn] using reaches_liftFrom (reaches_liftFrom positive 0) 0
  have htest : Reaches T
      (.app (.app (.app churchIsZero (church (v + 1))) (.var 1)) (.var 0)) :=
    reaches_appLeft (reaches_appLeft (reaches_appRight churchIsZero hw) _) _
  have hvar : Reaches T (.var 0) :=
    reaches_trans htest (headBlock_reaches (churchIsZero_positive_head v (.var 1) (.var 0)))
  have hstar := standardization T 0 hvar
  have hblock : Relation.TransGen HeadContract T (.var 0) := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hstar with heq | h
    · simp [T] at heq
    · exact h
  have hzero1 := substAt_scoped churchIsZero 0 (liftFrom 0 B) churchIsZero_closed
  have hzero2 := substAt_scoped churchIsZero 0 A churchIsZero_closed
  have once := headBlock_subst hblock 0 (liftFrom 0 B)
  have twice := headBlock_subst once 0 A
  simpa [T, W, substAt, liftBy, substAt_liftFrom, hzero1, hzero2] using twice

/-- The variable-headed single-argument prefix case of standardization.  It
    permits an unreduced argument; an exact-numeral head endpoint is false. -/
def VariableApplicationHeadPrefix : Prop :=
  ∀ t x n, Reaches t (.app (.var x) (church n)) →
    ∃ W, Relation.ReflTransGen HeadContract t (.app (.var x) W) ∧ Reaches W (church n)

/-- Ordinary CPS representation supplies observable search progress once the
    two explicit head-standardization lemmas are available. -/
theorem cpsRepresentation_searchHeadPositive
    (varStandardization : VariableHeadStandardization) (prefixStd : VariableApplicationHeadPrefix)
    {G : Term} {g : Nat →. Nat} (hg : CPSRepresents G g) (a start : Nat)
    (hpositive : ∀ j, ∃ v, v + 1 ∈ g (Nat.pair a (start + j))) :
    SearchHeadPositive G a start := by
  intro j K
  let I := symbolicSearchIndex start j
  let X : Term := .app G (.app (.app churchNatPair (church a)) I)
  let T : Term := .app X (.var 0)
  have hi : Scoped 0 I := symbolicSearchIndex_closed start j
  have hx : Scoped 0 X := ⟨hg.1, ⟨⟨churchNatPair_closed, church_closed a⟩, hi⟩⟩
  obtain ⟨v, hv⟩ := hpositive j
  have harg : Reaches (.app (.app churchNatPair (church a)) I) (church (Nat.pair a (start + j))) :=
    reaches_trans (reaches_appRight (.app churchNatPair (church a)) (symbolicSearchIndex_run start j))
      (churchNatPair_run a (start + j))
  have hinput : Reaches T (.app (.app G (church (Nat.pair a (start + j)))) (.var 0)) :=
    reaches_appLeft (reaches_appRight G harg) _
  have hcomputed := (hg.2 (Nat.pair a (start + j)) (.var 0)).1 (v + 1) hv
  obtain ⟨W, hprefix, hW⟩ := prefixStd T 0 (v + 1) (reaches_trans hinput hcomputed)
  have hxne : X ≠ .var 0 := by
    intro heq
    rw [heq] at hx
    simp [Scoped] at hx
  have hblock : Relation.TransGen HeadContract T (.app (.var 0) W) := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hprefix with heq | h
    · have hX : X = .var 0 := by
        change Term.app (.var 0) W = Term.app X (.var 0) at heq
        exact (Term.app.inj heq).1.symm
      exact False.elim (hxne hX)
    · exact h
  have hsubst := headBlock_subst hblock 0 K
  have hXsubst := substAt_scoped X 0 K hx
  have hhead : Relation.TransGen HeadContract (.app X K) (.app K (substAt 0 K W)) := by
    simpa [T, substAt, liftBy, hXsubst] using hsubst
  have hWsubst : Reaches (substAt 0 K W) (church (v + 1)) := by
    have hn := substAt_scoped (church (v + 1)) 0 K (church_closed _)
    simpa [hn] using reaches_subst hW 0 K
  exact ⟨substAt 0 K W, hhead, beta_positive_observable varStandardization hWsubst⟩

/-- The single outstanding metatheoretic dependency is standardization,
    split here into the three consequences used by the minimizer. -/
def HeadStandardizationObligations : Prop :=
  VariableHeadStandardization ∧ VariableApplicationHeadPrefix ∧ WeakNormalizationImpliesHeadAccessible

theorem cpsMinimize_code_of_head_standardization {G : Term} {f : Nat.Partrec.Code}
    (hg : CPSRepresents G (Nat.Partrec.Code.eval f)) (hstd : HeadStandardizationObligations) :
    CPSRepresents (cpsMinimize G) (Nat.Partrec.Code.eval (.rfind' f)) := by
  apply cpsMinimize_code_conditional hg hstd.2.2
  intro x hx
  exact cpsRepresentation_searchHeadPositive hstd.1 hstd.2.1 hg x.unpair.1 x.unpair.2 hx

#print axioms beta_positive_observable
#print axioms cpsRepresentation_searchHeadPositive
#print axioms cpsMinimize_code_of_head_standardization

end LambdaTuring
