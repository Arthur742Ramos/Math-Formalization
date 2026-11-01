/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.HeadReduction
public meta import LambdaTuring.HeadReduction

@[expose] public section

/- The positive zero-test head reduction follows the related Isabelle
   Lambda_CPS_Head_Minimization development. -/

namespace LambdaTuring

theorem headStep_into_block {t u : Term} (h : HeadContract t u) :
    Relation.TransGen HeadContract t u := .single h

/-- A positive numeral selects the second branch by nonempty head reduction,
    even when the branch terms are open. -/
theorem churchIsZero_positive_head (v : Nat) (A B : Term) :
    Relation.TransGen HeadContract
      (.app (.app (.app churchIsZero (church (v + 1))) A) B) B := by
  let N := church (v + 1)
  let R := substAt 1 zeroStep (churchBody v)
  let Q := substAt 0 pairFirstSelector R
  have hs0 := substAt_scoped zeroStep 0 N zeroStep_closed
  have ht0 := substAt_scoped pairFirstSelector 0 N pairFirstSelector_closed
  have h1 : HeadContract (.app churchIsZero N) (.app (.app N zeroStep) pairFirstSelector) := by
    have h := HeadContract.root (.app (.app (.var 0) zeroStep) pairFirstSelector) N
    simpa [churchIsZero, substAt, liftBy, hs0, ht0] using h
  have hz1 : liftBy 1 zeroStep = zeroStep := liftBy_closed 1 zeroStep_closed
  have h2 : HeadContract (.app N zeroStep) (.abs (.app zeroStep R)) := by
    have h := HeadContract.root (.abs (.app (.var 1) (churchBody v))) zeroStep
    simpa [N, church, churchBody, R, substAt, hz1] using h
  have hzs := substAt_scoped zeroStep 0 pairFirstSelector zeroStep_closed
  have h3 : HeadContract (.app (.abs (.app zeroStep R)) pairFirstSelector) (.app zeroStep Q) := by
    have h := HeadContract.root (.app zeroStep R) pairFirstSelector
    simpa [substAt, hzs, Q] using h
  have hfalse := substAt_scoped pairSecondSelector 0 Q pairSecondSelector_closed
  have h4 : HeadContract (.app zeroStep Q) pairSecondSelector := by
    have h := HeadContract.root pairSecondSelector Q
    simpa [zeroStep, hfalse] using h
  have h5 : HeadContract (.app pairSecondSelector A) (.abs (.var 0)) := by
    simpa [pairSecondSelector, substAt] using HeadContract.root (.abs (.var 0)) A
  have h6 : HeadContract (.app (.abs (.var 0)) B) B := by
    simpa [substAt, liftBy] using HeadContract.root (.var 0) B
  have h1' := HeadContract.appLeft B (HeadContract.appLeft A h1)
  have h2' := HeadContract.appLeft B (HeadContract.appLeft A (HeadContract.appLeft pairFirstSelector h2))
  have h3' := HeadContract.appLeft B (HeadContract.appLeft A h3)
  have h4' := HeadContract.appLeft B (HeadContract.appLeft A h4)
  have h5' := HeadContract.appLeft B h5
  exact (((((headStep_into_block h1').tail h2').tail h3').tail h4').tail h5').tail h6

def cpsSearchContTerm (G : Term) (a : Nat) (I K : Term) : Term :=
  .abs (.app (.app (.app churchIsZero (.var 0)) (.app (liftFrom 0 K) I))
    (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) (liftFrom 0 K)))

theorem cpsSearchContTerm_positive_head {G I : Term} (hg : Scoped 0 G) (hi : Scoped 0 I)
    (a v : Nat) (K : Term) :
    Relation.TransGen HeadContract (.app (cpsSearchContTerm G a I K) (church (v + 1)))
      (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) K) := by
  have hz := substAt_scoped churchIsZero 0 (church (v + 1)) churchIsZero_closed
  have hs := substAt_scoped churchSuccessor 0 (church (v + 1)) churchSuccessor_closed
  have hl := substAt_scoped (cpsSearchLoop G) 0 (church (v + 1)) (cpsSearchLoop_closed hg)
  have ha := substAt_scoped (church a) 0 (church (v + 1)) (church_closed a)
  have hI := substAt_scoped I 0 (church (v + 1)) hi
  have hK := substAt_liftFrom K 0 (church (v + 1))
  have h : HeadContract (.app (cpsSearchContTerm G a I K) (church (v + 1)))
      (.app (.app (.app churchIsZero (church (v + 1))) (.app K I))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) K)) := by
    simpa [cpsSearchContTerm, substAt, liftBy, hz, hs, hl, ha, hI, hK] using
      (HeadContract.root (.app (.app (.app churchIsZero (.var 0)) (.app (liftFrom 0 K) I))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) (liftFrom 0 K)))
        (church (v + 1)))
  exact (headStep_into_block h).trans (churchIsZero_positive_head v _ _)

def HeadPositiveResult (V : Term) : Prop :=
  ∀ A B, Relation.TransGen HeadContract (.app (.app (.app churchIsZero V) A) B) B

theorem church_positive_result (v : Nat) : HeadPositiveResult (church (v + 1)) :=
  churchIsZero_positive_head v

theorem cpsSearchContTerm_observable_head {G I : Term} (hg : Scoped 0 G) (hi : Scoped 0 I)
    (a : Nat) (V K : Term) (hv : HeadPositiveResult V) :
    Relation.TransGen HeadContract (.app (cpsSearchContTerm G a I K) V)
      (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) K) := by
  have hz := substAt_scoped churchIsZero 0 V churchIsZero_closed
  have hs := substAt_scoped churchSuccessor 0 V churchSuccessor_closed
  have hl := substAt_scoped (cpsSearchLoop G) 0 V (cpsSearchLoop_closed hg)
  have ha := substAt_scoped (church a) 0 V (church_closed a)
  have hI := substAt_scoped I 0 V hi
  have hK := substAt_liftFrom K 0 V
  have h : HeadContract (.app (cpsSearchContTerm G a I K) V)
      (.app (.app (.app churchIsZero V) (.app K I))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) K)) := by
    simpa [cpsSearchContTerm, substAt, liftBy, hz, hs, hl, ha, hI, hK] using
      (HeadContract.root (.app (.app (.app churchIsZero (.var 0)) (.app (liftFrom 0 K) I))
        (.app (.app (.app (cpsSearchLoop G) (church a)) (.app churchSuccessor I)) (liftFrom 0 K))) V)
  exact (headStep_into_block h).trans (hv _ _)

/-- The search loop reaches its symbolic test by nonempty head reduction. -/
theorem cpsSearchLoop_head_dispatch {G I : Term} (hg : Scoped 0 G) (hi : Scoped 0 I)
    (a : Nat) (K : Term) :
    Relation.TransGen HeadContract (.app (.app (.app (cpsSearchLoop G) (church a)) I) K)
      (.app (.app G (.app (.app churchNatPair (church a)) I)) (cpsSearchContTerm G a I K)) := by
  let L := cpsSearchLoop G
  have hL : Scoped 0 L := cpsSearchLoop_closed hg
  have sG (d : Nat) (t : Term) := substAt_scoped G d t (scoped_mono hg (Nat.zero_le d))
  have sL (d : Nat) (t : Term) := substAt_scoped L d t (scoped_mono hL (Nat.zero_le d))
  have sP (d : Nat) (t : Term) := substAt_scoped churchNatPair d t (scoped_mono churchNatPair_closed (Nat.zero_le d))
  have sZ (d : Nat) (t : Term) := substAt_scoped churchIsZero d t (scoped_mono churchIsZero_closed (Nat.zero_le d))
  have sS (d : Nat) (t : Term) := substAt_scoped churchSuccessor d t (scoped_mono churchSuccessor_closed (Nat.zero_le d))
  have sA (d : Nat) (t : Term) := substAt_scoped (church a) d t (scoped_mono (church_closed a) (Nat.zero_le d))
  have sI (d : Nat) (t : Term) := substAt_scoped I d t (scoped_mono hi (Nat.zero_le d))
  have lL (d : Nat) := liftBy_closed d hL
  have lA (d : Nat) := liftBy_closed d (church_closed a)
  have lI (d : Nat) := liftBy_closed d hi
  let T1 : Term := .abs (.abs (.abs
    (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
        (.app (.app (.app L (.var 3)) (.app churchSuccessor (.var 2))) (.var 1)))))))
  let T2 : Term := .abs (.abs
    (.app (.app G (.app (.app churchNatPair (church a)) (.var 1)))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
        (.app (.app (.app L (church a)) (.app churchSuccessor (.var 2))) (.var 1))))))
  let T3 : Term := .abs
    (.app (.app G (.app (.app churchNatPair (church a)) I))
      (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) I))
        (.app (.app (.app L (church a)) (.app churchSuccessor I)) (.var 1)))))
  have h0 : HeadContract L (.app (cpsSearchBody G) L) := lambdaFix_head_unfold (cpsSearchBody_closed hg)
  have h1 : HeadContract (.app (cpsSearchBody G) L) T1 := by
    simpa [cpsSearchBody, T1, substAt, sG, sP, sZ, sS, lL] using
      (HeadContract.root (.abs (.abs (.abs
        (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app (.var 4) (.var 3)) (.app churchSuccessor (.var 2))) (.var 1)))))))) L)
  have h2 : HeadContract (.app T1 (church a)) T2 := by
    simpa [T1, T2, substAt, sG, sL, sP, sZ, sS, lA] using
      (HeadContract.root (.abs (.abs
        (.app (.app G (.app (.app churchNatPair (.var 2)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app L (.var 3)) (.app churchSuccessor (.var 2))) (.var 1))))))) (church a))
  have h3 : HeadContract (.app T2 I) T3 := by
    simpa [T2, T3, substAt, sG, sL, sP, sZ, sS, sA, lI] using
      (HeadContract.root (.abs
        (.app (.app G (.app (.app churchNatPair (church a)) (.var 1)))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) (.var 2)))
            (.app (.app (.app L (church a)) (.app churchSuccessor (.var 2))) (.var 1)))))) I)
  have h4 : HeadContract (.app T3 K)
      (.app (.app G (.app (.app churchNatPair (church a)) I)) (cpsSearchContTerm G a I K)) := by
    simpa [T3, cpsSearchContTerm, substAt, liftBy, sG, sL, sP, sZ, sS, sA, sI] using
      (HeadContract.root
        (.app (.app G (.app (.app churchNatPair (church a)) I))
          (.abs (.app (.app (.app churchIsZero (.var 0)) (.app (.var 1) I))
            (.app (.app (.app L (church a)) (.app churchSuccessor I)) (.var 1))))) K)
  exact ((((headStep_into_block (.appLeft K (.appLeft I (.appLeft (church a) h0)))).tail
    (.appLeft K (.appLeft I (.appLeft (church a) h1)))).tail
    (.appLeft K (.appLeft I h2))).tail (.appLeft K h3)).tail h4

/-- Unevaluated indices let each positive branch advance by head reduction. -/
def symbolicSearchIndex (start : Nat) : Nat → Term
  | 0 => church start
  | n + 1 => .app churchSuccessor (symbolicSearchIndex start n)

theorem symbolicSearchIndex_closed (start n : Nat) : Scoped 0 (symbolicSearchIndex start n) := by
  induction n with
  | zero => exact church_closed start
  | succ n ih => exact ⟨churchSuccessor_closed, ih⟩

theorem symbolicSearchIndex_run (start n : Nat) :
    Reaches (symbolicSearchIndex start n) (church (start + n)) := by
  induction n with
  | zero => simpa [symbolicSearchIndex] using Reaches.refl (church start)
  | succ n ih =>
    exact reaches_trans (reaches_appRight churchSuccessor ih) (churchSuccessor_run (start + n))

/-- A strong, explicitly stated head-progress premise for a positive test. -/
def SearchHeadPositive (G : Term) (a start : Nat) : Prop :=
  ∀ j K, ∃ V, Relation.TransGen HeadContract
    (.app (.app G (.app (.app churchNatPair (church a)) (symbolicSearchIndex start j))) K)
    (.app K V) ∧ HeadPositiveResult V

theorem cpsSearchLoop_head_positive_not_accessible {G : Term} (hg : Scoped 0 G)
    (a start : Nat) (K : Term) (hp : SearchHeadPositive G a start) :
    ¬ HeadAccessible (.app (.app (.app (cpsSearchLoop G) (church a)) (church start)) K) := by
  let T : Nat → Term := fun j => .app (.app (.app (cpsSearchLoop G) (church a)) (symbolicSearchIndex start j)) K
  have run : ∀ j, Relation.TransGen HeadContract (T j) (T (j + 1)) := by
    intro j
    let I := symbolicSearchIndex start j
    let C := cpsSearchContTerm G a I K
    have hi : Scoped 0 I := symbolicSearchIndex_closed start j
    obtain ⟨V, hv, hV⟩ := hp j C
    have hd := cpsSearchLoop_head_dispatch hg hi a K
    have hc := cpsSearchContTerm_observable_head hg hi a V K hV
    exact hd.trans (hv.trans hc)
  exact headBlocksInfinite_not_accessible T run

/-- This property is a remaining standardization obligation, not an axiom. -/
def WeakNormalizationImpliesHeadAccessible : Prop :=
  ∀ t, (∃ N, Reaches t N ∧ ¬ ∃ u, Beta N u) → HeadAccessible t

theorem cpsSearchLoop_head_positive_no_normal {G : Term}
    (standardization : WeakNormalizationImpliesHeadAccessible) (hg : Scoped 0 G)
    (a start : Nat) (K : Term) (hp : SearchHeadPositive G a start) :
    ¬ ∃ N, Reaches (.app (.app (.app (cpsSearchLoop G) (church a)) (church start)) K) N ∧
      ¬ ∃ u, Beta N u := by
  intro hn
  exact cpsSearchLoop_head_positive_not_accessible hg a start K hp (standardization _ hn)

#print axioms cpsSearchLoop_head_dispatch
#print axioms churchIsZero_positive_head
#print axioms cpsSearchContTerm_positive_head
#print axioms cpsSearchLoop_head_positive_no_normal

end LambdaTuring
