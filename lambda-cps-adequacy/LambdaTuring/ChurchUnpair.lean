/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.PairEnumeration
public meta import LambdaTuring.PairEnumeration

@[expose] public section

namespace LambdaTuring

/-- A closed constructor for Church pairs, usable inside open lambda terms. -/
def churchPairMake : Term := .abs (.abs (.abs (.app (.app (.var 0) (.var 2)) (.var 1))))

theorem churchPairMake_closed : Scoped 0 churchPairMake := by simp [churchPairMake, Scoped]

theorem churchPairMake_run {a b : Term} (ha : Scoped 0 a) (hb : Scoped 0 b) :
    Reaches (.app (.app churchPairMake a) b) (churchPair a b) := by
  have ha2 : liftBy 2 a = a := liftBy_closed 2 ha
  have h1 : Beta (.app churchPairMake a) (.abs (.abs (.app (.app (.var 0) a) (.var 1)))) := by
    simpa [churchPairMake, substAt, ha2] using
      (Beta.contract (.abs (.abs (.app (.app (.var 0) (.var 2)) (.var 1)))) a)
  have ha1 := substAt_scoped a 1 b (scoped_mono ha (Nat.zero_le 1))
  have hb1 : liftBy 1 b = b := liftBy_closed 1 hb
  have h2 : Beta (.app (.abs (.abs (.app (.app (.var 0) a) (.var 1)))) b) (churchPair a b) := by
    simpa [churchPair, substAt, ha1, hb1] using
      (Beta.contract (.abs (.app (.app (.var 0) a) (.var 1))) b)
  exact .step (.appLeft h1) (.step h2 (.refl _))

theorem reaches_app_both {f f' x x' : Term} (hf : Reaches f f') (hx : Reaches x x') :
    Reaches (.app f x) (.app f' x') :=
  reaches_trans (reaches_appLeft hf x) (reaches_appRight f' hx)

def chooseTerm (cond yes no : Term) : Term := .app (.app cond yes) no
def pairApply (a b : Term) : Term := .app (.app churchPairMake a) b
def lessApply (a b : Term) : Term := .app (.app churchLess a) b
def successorApply (a : Term) : Term := .app churchSuccessor a

/-- The four cases mirror `nextNumericPair`, using Church booleans and pairs. -/
def nextNumericExpr (a b : Term) : Term :=
  chooseTerm (lessApply a b)
    (chooseTerm (lessApply (successorApply a) b)
      (pairApply (successorApply a) b) (pairApply b (church 0)))
    (chooseTerm (lessApply b a)
      (pairApply a (successorApply b)) (pairApply (church 0) (successorApply a)))

def nextPairExpr (p : Term) : Term :=
  nextNumericExpr (.app pairFirst p) (.app pairSecond p)

def churchNextPair : Term := .abs (nextPairExpr (.var 0))

theorem churchNextPair_closed : Scoped 0 churchNextPair := by
  have hf := scoped_mono pairFirst_closed (Nat.zero_le 1)
  have hs := scoped_mono pairSecond_closed (Nat.zero_le 1)
  have hc := scoped_mono churchPairMake_closed (Nat.zero_le 1)
  have hl := scoped_mono churchLess_closed (Nat.zero_le 1)
  have hu := scoped_mono churchSuccessor_closed (Nat.zero_le 1)
  have hz := scoped_mono (church_closed 0) (Nat.zero_le 1)
  simp [churchNextPair, nextPairExpr, nextNumericExpr, chooseTerm, pairApply,
    lessApply, successorApply, Scoped, hf, hs, hc, hl, hu, hz]

theorem churchNextPair_beta (p : Term) :
    Beta (.app churchNextPair p) (nextPairExpr p) := by
  have hf := substAt_scoped pairFirst 0 p pairFirst_closed
  have hs := substAt_scoped pairSecond 0 p pairSecond_closed
  have hc := substAt_scoped churchPairMake 0 p churchPairMake_closed
  have hl := substAt_scoped churchLess 0 p churchLess_closed
  have hu := substAt_scoped churchSuccessor 0 p churchSuccessor_closed
  have hz := substAt_scoped (church 0) 0 p (church_closed 0)
  simpa [churchNextPair, nextPairExpr, nextNumericExpr, chooseTerm, pairApply,
    lessApply, successorApply, substAt, liftBy, hf, hs, hc, hl, hu, hz] using
    (Beta.contract (nextPairExpr (.var 0)) p)

theorem nextPairExpr_reaches (a b : Nat) :
    Reaches (nextPairExpr (churchPair (church a) (church b))) (nextNumericExpr (church a) (church b)) := by
  have ha := pairFirst_run (church_closed a) (church_closed b)
  have hb := pairSecond_run (church_closed a) (church_closed b)
  unfold nextPairExpr nextNumericExpr chooseTerm pairApply lessApply successorApply
  repeat' first | exact ha | exact hb | exact Reaches.refl _ | apply reaches_app_both

theorem chooseTerm_bool (p : Prop) [Decidable p] {a b : Term} (ha : Scoped 0 a) :
    Reaches (chooseTerm (if p then pairFirstSelector else pairSecondSelector) a b) (if p then a else b) := by
  by_cases h : p
  · simpa [chooseTerm, h] using pairFirstSelector_run ha b
  · simpa [chooseTerm, h] using pairSecondSelector_run a b

theorem pairApply_church (a b : Nat) :
    Reaches (pairApply (church a) (church b)) (churchPair (church a) (church b)) :=
  churchPairMake_run (church_closed a) (church_closed b)

theorem pairApply_succ_left (a b : Nat) :
    Reaches (pairApply (successorApply (church a)) (church b)) (churchPair (church (a + 1)) (church b)) := by
  apply reaches_trans (reaches_appLeft (reaches_appRight churchPairMake (churchSuccessor_run a)) (church b))
  exact pairApply_church (a + 1) b

theorem pairApply_succ_right (a b : Nat) :
    Reaches (pairApply (church a) (successorApply (church b))) (churchPair (church a) (church (b + 1))) := by
  apply reaches_trans (reaches_appRight (.app churchPairMake (church a)) (churchSuccessor_run b))
  exact pairApply_church a (b + 1)

theorem nextNumericExpr_run (a b : Nat) :
    Reaches (nextNumericExpr (church a) (church b))
      (churchPair (church (nextNumericPair a b).1) (church (nextNumericPair a b).2)) := by
  let p1 := churchPair (church (a + 1)) (church b)
  let p2 := churchPair (church b) (church 0)
  let p3 := churchPair (church a) (church (b + 1))
  let p4 := churchPair (church 0) (church (a + 1))
  let c1 := if a < b then pairFirstSelector else pairSecondSelector
  let c2 := if a + 1 < b then pairFirstSelector else pairSecondSelector
  let c3 := if b < a then pairFirstSelector else pairSecondSelector
  have hc1 : Reaches (lessApply (church a) (church b)) c1 := churchLess_run a b
  have hc2 : Reaches (lessApply (successorApply (church a)) (church b)) c2 :=
    reaches_trans (reaches_appLeft (reaches_appRight churchLess (churchSuccessor_run a)) (church b))
      (churchLess_run (a + 1) b)
  have hc3 : Reaches (lessApply (church b) (church a)) c3 := churchLess_run b a
  have hp1 : Reaches (pairApply (successorApply (church a)) (church b)) p1 := pairApply_succ_left a b
  have hp2 : Reaches (pairApply (church b) (church 0)) p2 := pairApply_church b 0
  have hp3 : Reaches (pairApply (church a) (successorApply (church b))) p3 := pairApply_succ_right a b
  have hp4 : Reaches (pairApply (church 0) (successorApply (church a))) p4 := pairApply_succ_right 0 a
  have hp1c : Scoped 0 p1 := churchPair_closed (church_closed (a + 1)) (church_closed b)
  have hp3c : Scoped 0 p3 := churchPair_closed (church_closed a) (church_closed (b + 1))
  have hresolved : Reaches (nextNumericExpr (church a) (church b))
      (chooseTerm c1 (chooseTerm c2 p1 p2) (chooseTerm c3 p3 p4)) := by
    unfold nextNumericExpr chooseTerm
    repeat' first | exact hc1 | exact hc2 | exact hc3 | exact hp1 | exact hp2 | exact hp3 | exact hp4 |
      exact Reaches.refl _ | apply reaches_app_both
  have hleft : Reaches (chooseTerm c2 p1 p2) (if a + 1 < b then p1 else p2) :=
    chooseTerm_bool (a + 1 < b) hp1c
  have hright : Reaches (chooseTerm c3 p3 p4) (if b < a then p3 else p4) :=
    chooseTerm_bool (b < a) hp3c
  have hselected : Reaches (chooseTerm c1 (chooseTerm c2 p1 p2) (chooseTerm c3 p3 p4))
      (chooseTerm c1 (if a + 1 < b then p1 else p2) (if b < a then p3 else p4)) :=
    reaches_app_both (reaches_app_both (Reaches.refl c1) hleft) hright
  have hclosed : Scoped 0 (if a + 1 < b then p1 else p2) := by
    split
    · exact hp1c
    · exact churchPair_closed (church_closed b) (church_closed 0)
  have houter := chooseTerm_bool (a < b) (b := (if b < a then p3 else p4)) hclosed
  have hout : (if a < b then (if a + 1 < b then p1 else p2) else (if b < a then p3 else p4)) =
      churchPair (church (nextNumericPair a b).1) (church (nextNumericPair a b).2) := by
    by_cases h1 : a < b <;> by_cases h2 : a + 1 < b <;> by_cases h3 : b < a <;>
      simp [nextNumericPair, h1, h2, h3, p1, p2, p3, p4]
  rw [hout] at houter
  exact reaches_trans hresolved (reaches_trans hselected houter)

theorem churchNextPair_run (a b : Nat) :
    Reaches (.app churchNextPair (churchPair (church a) (church b)))
      (churchPair (church (nextNumericPair a b).1) (church (nextNumericPair a b).2)) :=
  .step (churchNextPair_beta _) (reaches_trans (nextPairExpr_reaches a b) (nextNumericExpr_run a b))

def unpairSeed : Term := churchPair (church 0) (church 0)

theorem unpairSeed_closed : Scoped 0 unpairSeed :=
  churchPair_closed (church_closed 0) (church_closed 0)

theorem churchUnpair_iter (n : Nat) :
    Reaches (churchIter n churchNextPair unpairSeed)
      (churchPair (church n.unpair.1) (church n.unpair.2)) := by
  induction n with
  | zero => simpa [churchIter, unpairSeed, Nat.unpair_zero] using Reaches.refl unpairSeed
  | succ n ih =>
    have h := reaches_trans (reaches_appRight churchNextPair ih)
      (churchNextPair_run n.unpair.1 n.unpair.2)
    simpa [churchIter, unpair_succ] using h

/-- Iterates the numeric-pair successor, implementing Mathlib's `Nat.unpair`. -/
def churchUnpair : Term := .abs (.app (.app (.var 0) churchNextPair) unpairSeed)

theorem churchUnpair_closed : Scoped 0 churchUnpair := by
  have hn := scoped_mono churchNextPair_closed (Nat.zero_le 1)
  have hz := scoped_mono unpairSeed_closed (Nat.zero_le 1)
  simp [churchUnpair, Scoped, hn, hz]

theorem churchUnpair_run (n : Nat) :
    Reaches (.app churchUnpair (church n))
      (churchPair (church n.unpair.1) (church n.unpair.2)) := by
  have hn := substAt_scoped churchNextPair 0 (church n) churchNextPair_closed
  have hz := substAt_scoped unpairSeed 0 (church n) unpairSeed_closed
  have hbeta : Beta (.app churchUnpair (church n))
      (.app (.app (church n) churchNextPair) unpairSeed) := by
    simpa [churchUnpair, substAt, liftBy, hn, hz] using
      (Beta.contract (.app (.app (.var 0) churchNextPair) unpairSeed) (church n))
  exact .step hbeta (reaches_trans (church_iterates n churchNextPair unpairSeed) (churchUnpair_iter n))

def churchNumericLeft : Term := .abs (.app pairFirst (.app churchUnpair (.var 0)))
def churchNumericRight : Term := .abs (.app pairSecond (.app churchUnpair (.var 0)))

theorem churchNumericLeft_closed : Scoped 0 churchNumericLeft := by
  have hf := scoped_mono pairFirst_closed (Nat.zero_le 1)
  have hu := scoped_mono churchUnpair_closed (Nat.zero_le 1)
  simp [churchNumericLeft, Scoped, hf, hu]

theorem churchNumericRight_closed : Scoped 0 churchNumericRight := by
  have hf := scoped_mono pairSecond_closed (Nat.zero_le 1)
  have hu := scoped_mono churchUnpair_closed (Nat.zero_le 1)
  simp [churchNumericRight, Scoped, hf, hu]

theorem churchNumericLeft_run (n : Nat) :
    Reaches (.app churchNumericLeft (church n)) (church n.unpair.1) := by
  have hf := substAt_scoped pairFirst 0 (church n) pairFirst_closed
  have hu := substAt_scoped churchUnpair 0 (church n) churchUnpair_closed
  have hb : Beta (.app churchNumericLeft (church n)) (.app pairFirst (.app churchUnpair (church n))) := by
    simpa [churchNumericLeft, substAt, liftBy, hf, hu] using
      (Beta.contract (.app pairFirst (.app churchUnpair (.var 0))) (church n))
  exact .step hb (reaches_trans (reaches_appRight pairFirst (churchUnpair_run n))
    (pairFirst_run (church_closed _) (church_closed _)))

theorem churchNumericRight_run (n : Nat) :
    Reaches (.app churchNumericRight (church n)) (church n.unpair.2) := by
  have hf := substAt_scoped pairSecond 0 (church n) pairSecond_closed
  have hu := substAt_scoped churchUnpair 0 (church n) churchUnpair_closed
  have hb : Beta (.app churchNumericRight (church n)) (.app pairSecond (.app churchUnpair (church n))) := by
    simpa [churchNumericRight, substAt, liftBy, hf, hu] using
      (Beta.contract (.app pairSecond (.app churchUnpair (.var 0))) (church n))
  exact .step hb (reaches_trans (reaches_appRight pairSecond (churchUnpair_run n))
    (pairSecond_run (church_closed _) (church_closed _)))

#print axioms churchNumericLeft_run
#print axioms churchNumericRight_run
#print axioms churchPairMake_run
#print axioms churchNextPair_beta
#print axioms nextPairExpr_reaches
#print axioms nextNumericExpr_run

end LambdaTuring
