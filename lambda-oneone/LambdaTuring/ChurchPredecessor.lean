/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchPairs
public meta import LambdaTuring.ChurchPairs

@[expose] public section

/- The indexed Church-pair construction is related to the predecessor and
   primitive-recursion constructions in the Isabelle Lambda_Church_Pairs theory. -/

namespace LambdaTuring

theorem churchPair_congr {a a' b b' : Term} (ha : Reaches a a') (hb : Reaches b b') :
    Reaches (churchPair a b) (churchPair a' b') := by
  apply reaches_trans (reaches_abs (reaches_appLeft (reaches_appRight (.var 0) ha) b))
  exact reaches_abs (reaches_appRight (.app (.var 0) a') hb)

/-- Transform the pair `(old,current)` to `(current,current+1)`. -/
def predecessorStep : Term :=
  .abs (.abs (.app (.app (.var 0) (.app pairSecond (.var 1)))
    (.app churchSuccessor (.app pairSecond (.var 1)))))

theorem predecessorStep_closed : Scoped 0 predecessorStep := by
  simp [predecessorStep, pairSecond, pairSecondSelector, churchSuccessor, Scoped]

theorem predecessorStep_run (i v : Nat) :
    Reaches (.app predecessorStep (churchPair (church i) (church v)))
      (churchPair (church v) (church (v + 1))) := by
  let p := churchPair (church i) (church v)
  have hp : Scoped 0 p := churchPair_closed (church_closed i) (church_closed v)
  have hshift : liftBy 1 p = p := liftBy_closed 1 hp
  have hsecond := substAt_scoped pairSecond 1 p (scoped_mono pairSecond_closed (Nat.zero_le 1))
  have hsucc := substAt_scoped churchSuccessor 1 p (scoped_mono churchSuccessor_closed (Nat.zero_le 1))
  have hb : Beta (.app predecessorStep p)
      (churchPair (.app pairSecond p) (.app churchSuccessor (.app pairSecond p))) := by
    simpa [predecessorStep, churchPair, substAt, hshift, hsecond, hsucc] using
      (Beta.contract (.abs (.app (.app (.var 0) (.app pairSecond (.var 1)))
        (.app churchSuccessor (.app pairSecond (.var 1))))) p)
  have hsecondRun : Reaches (.app pairSecond p) (church v) :=
    pairSecond_run (church_closed i) (church_closed v)
  have hsuccRun : Reaches (.app churchSuccessor (.app pairSecond p)) (church (v + 1)) :=
    reaches_trans (reaches_appRight churchSuccessor hsecondRun) (churchSuccessor_run v)
  exact .step hb (churchPair_congr hsecondRun hsuccRun)

def predecessorSeed : Term := churchPair (church 0) (church 0)

theorem predecessorSeed_closed : Scoped 0 predecessorSeed :=
  churchPair_closed (church_closed 0) (church_closed 0)

theorem predecessorStep_iterate (n : Nat) :
    Reaches (churchIter n predecessorStep predecessorSeed)
      (churchPair (church (n - 1)) (church n)) := by
  induction n with
  | zero => simpa [churchIter, predecessorSeed] using Reaches.refl predecessorSeed
  | succ n ih =>
    have h := reaches_trans (reaches_appRight predecessorStep ih) (predecessorStep_run (n - 1) n)
    simpa [churchIter] using h

/-- Church predecessor, with zero mapped to zero. -/
def churchPredecessor : Term :=
  .abs (.app pairFirst (.app (.app (.var 0) predecessorStep) predecessorSeed))

theorem churchPredecessor_closed : Scoped 0 churchPredecessor := by
  change Scoped 1 (.app pairFirst (.app (.app (.var 0) predecessorStep) predecessorSeed))
  exact ⟨scoped_mono pairFirst_closed (Nat.zero_le 1),
    ⟨⟨by simp [Scoped], scoped_mono predecessorStep_closed (Nat.zero_le 1)⟩,
      scoped_mono predecessorSeed_closed (Nat.zero_le 1)⟩⟩

theorem churchPredecessor_run (n : Nat) :
    Reaches (.app churchPredecessor (church n)) (church (n - 1)) := by
  have hf := substAt_scoped pairFirst 0 (church n) pairFirst_closed
  have hs := substAt_scoped predecessorStep 0 (church n) predecessorStep_closed
  have hz := substAt_scoped predecessorSeed 0 (church n) predecessorSeed_closed
  have hb : Beta (.app churchPredecessor (church n))
      (.app pairFirst (.app (.app (church n) predecessorStep) predecessorSeed)) := by
    simpa [churchPredecessor, substAt, liftBy, hf, hs, hz] using
      (Beta.contract (.app pairFirst (.app (.app (.var 0) predecessorStep) predecessorSeed)) (church n))
  apply Reaches.step hb
  apply reaches_trans (reaches_appRight pairFirst (church_iterates n predecessorStep predecessorSeed))
  apply reaches_trans (reaches_appRight pairFirst (predecessorStep_iterate n))
  exact pairFirst_run (church_closed (n - 1)) (church_closed n)

theorem churchPredecessor_represents :
    Represents churchPredecessor (fun n => Part.some (n - 1)) := by
  constructor
  · exact churchPredecessor_closed
  · intro n
    rw [numericalValue_some_iff]
    exact churchPredecessor_run n

theorem predecessor_iterate (n a : Nat) :
    Reaches (churchIter n churchPredecessor (church a)) (church (a - n)) := by
  induction n with
  | zero => simpa [churchIter] using Reaches.refl (church a)
  | succ n ih =>
    have h := reaches_trans (reaches_appRight churchPredecessor ih) (churchPredecessor_run (a - n))
    simpa [churchIter, Nat.sub_sub] using h

/-- Truncated subtraction of Church numerals. -/
def churchSubtract : Term :=
  .abs (.abs (.app (.app (.var 0) churchPredecessor) (.var 1)))

theorem churchSubtract_closed : Scoped 0 churchSubtract := by
  change Scoped 2 (.app (.app (.var 0) churchPredecessor) (.var 1))
  exact ⟨⟨by simp [Scoped], scoped_mono churchPredecessor_closed (Nat.zero_le 2)⟩, by simp [Scoped]⟩

theorem churchSubtract_run (a b : Nat) :
    Reaches (.app (.app churchSubtract (church a)) (church b)) (church (a - b)) := by
  have hp1 := substAt_scoped churchPredecessor 1 (church a)
    (scoped_mono churchPredecessor_closed (Nat.zero_le 1))
  have ha1 : liftBy 1 (church a) = church a := liftBy_closed 1 (church_closed a)
  have hb1 : Beta (.app churchSubtract (church a))
      (.abs (.app (.app (.var 0) churchPredecessor) (church a))) := by
    simpa [churchSubtract, substAt, hp1, ha1] using
      (Beta.contract (.abs (.app (.app (.var 0) churchPredecessor) (.var 1))) (church a))
  have hp0 := substAt_scoped churchPredecessor 0 (church b) churchPredecessor_closed
  have ha0 := substAt_scoped (church a) 0 (church b) (church_closed a)
  have hb2 : Beta (.app (.abs (.app (.app (.var 0) churchPredecessor) (church a))) (church b))
      (.app (.app (church b) churchPredecessor) (church a)) := by
    simpa [substAt, liftBy, hp0, ha0] using
      (Beta.contract (.app (.app (.var 0) churchPredecessor) (church a)) (church b))
  apply Reaches.step (.appLeft hb1)
  apply Reaches.step hb2
  exact reaches_trans (church_iterates b churchPredecessor (church a)) (predecessor_iterate b a)

theorem churchSubtract_represents : BinaryRepresents churchSubtract (· - ·) := by
  constructor
  · exact churchSubtract_closed
  · intro a b m
    constructor
    · intro h
      exact numeral_result_unique h (churchSubtract_run a b)
    · intro h
      subst m
      exact churchSubtract_run a b

/-- Church boolean test for strict order: `a < b` iff `(a+1)-b = 0`. -/
def churchLess : Term :=
  .abs (.abs (.app churchIsZero
    (.app (.app churchSubtract (.app churchSuccessor (.var 1))) (.var 0))))

theorem churchLess_closed : Scoped 0 churchLess := by
  change Scoped 2 (.app churchIsZero (.app (.app churchSubtract (.app churchSuccessor (.var 1))) (.var 0)))
  exact ⟨scoped_mono churchIsZero_closed (Nat.zero_le 2),
    ⟨⟨scoped_mono churchSubtract_closed (Nat.zero_le 2),
       ⟨scoped_mono churchSuccessor_closed (Nat.zero_le 2), by simp [Scoped]⟩⟩, by simp [Scoped]⟩⟩

theorem churchLess_run (a b : Nat) :
    Reaches (.app (.app churchLess (church a)) (church b))
      (if a < b then pairFirstSelector else pairSecondSelector) := by
  have hz1 := substAt_scoped churchIsZero 1 (church a) (scoped_mono churchIsZero_closed (Nat.zero_le 1))
  have hsub1 := substAt_scoped churchSubtract 1 (church a) (scoped_mono churchSubtract_closed (Nat.zero_le 1))
  have hs1 := substAt_scoped churchSuccessor 1 (church a) (scoped_mono churchSuccessor_closed (Nat.zero_le 1))
  have ha1 : liftBy 1 (church a) = church a := liftBy_closed 1 (church_closed a)
  have hb1 : Beta (.app churchLess (church a))
      (.abs (.app churchIsZero (.app (.app churchSubtract (.app churchSuccessor (church a))) (.var 0)))) := by
    simpa [churchLess, substAt, hz1, hsub1, hs1, ha1] using
      (Beta.contract (.abs (.app churchIsZero
        (.app (.app churchSubtract (.app churchSuccessor (.var 1))) (.var 0)))) (church a))
  have hz0 := substAt_scoped churchIsZero 0 (church b) churchIsZero_closed
  have hsub0 := substAt_scoped churchSubtract 0 (church b) churchSubtract_closed
  have hs0 := substAt_scoped churchSuccessor 0 (church b) churchSuccessor_closed
  have ha0 := substAt_scoped (church a) 0 (church b) (church_closed a)
  have hb2 : Beta
      (.app (.abs (.app churchIsZero (.app (.app churchSubtract (.app churchSuccessor (church a))) (.var 0)))) (church b))
      (.app churchIsZero (.app (.app churchSubtract (.app churchSuccessor (church a))) (church b))) := by
    simpa [substAt, liftBy, hz0, hsub0, hs0, ha0] using
      (Beta.contract (.app churchIsZero (.app (.app churchSubtract (.app churchSuccessor (church a))) (.var 0))) (church b))
  have harg : Reaches (.app (.app churchSubtract (.app churchSuccessor (church a))) (church b))
      (church ((a + 1) - b)) :=
    reaches_trans (reaches_appLeft (reaches_appRight churchSubtract (churchSuccessor_run a)) (church b))
      (churchSubtract_run (a + 1) b)
  have hresult := reaches_trans (reaches_appRight churchIsZero harg) (churchIsZero_run ((a + 1) - b))
  have hzero : (a + 1) - b = 0 ↔ a < b := by omega
  apply Reaches.step (.appLeft hb1)
  apply Reaches.step hb2
  simpa only [hzero] using hresult

/-- The two branches of Mathlib's square-based numerical pairing formula. -/
def natPairExpr (a b : Term) : Term :=
  .app (.app (.app (.app churchLess a) b)
    (.app (.app churchAdd (.app (.app churchMultiply b) b)) a))
    (.app (.app churchAdd (.app (.app churchAdd (.app (.app churchMultiply a) a)) a)) b)

theorem subst_natPairExpr (depth : Nat) (value a b : Term) :
    substAt depth value (natPairExpr a b) = natPairExpr (substAt depth value a) (substAt depth value b) := by
  have hl := substAt_scoped churchLess depth value (scoped_mono churchLess_closed (Nat.zero_le depth))
  have ha := substAt_scoped churchAdd depth value (scoped_mono churchAdd_closed (Nat.zero_le depth))
  have hm := substAt_scoped churchMultiply depth value (scoped_mono churchMultiply_closed (Nat.zero_le depth))
  simp [natPairExpr, substAt, hl, ha, hm]

/-- A closed Church program computing Mathlib's actual `Nat.pair`. -/
def churchNatPair : Term := .abs (.abs (natPairExpr (.var 1) (.var 0)))

theorem churchNatPair_closed : Scoped 0 churchNatPair := by
  have hl := scoped_mono churchLess_closed (Nat.zero_le 2)
  have ha := scoped_mono churchAdd_closed (Nat.zero_le 2)
  have hm := scoped_mono churchMultiply_closed (Nat.zero_le 2)
  change Scoped 2 (natPairExpr (.var 1) (.var 0))
  simp [natPairExpr, Scoped, hl, ha, hm]

theorem churchNatPair_run (a b : Nat) :
    Reaches (.app (.app churchNatPair (church a)) (church b)) (church (Nat.pair a b)) := by
  have ha1 : liftBy 1 (church a) = church a := liftBy_closed 1 (church_closed a)
  have h1 : Beta (.app churchNatPair (church a)) (.abs (natPairExpr (church a) (.var 0))) := by
    have h := Beta.contract (.abs (natPairExpr (.var 1) (.var 0))) (church a)
    change Beta (.app churchNatPair (church a)) (.abs (substAt 1 (church a) (natPairExpr (.var 1) (.var 0)))) at h
    rw [subst_natPairExpr] at h
    simpa [substAt, ha1] using h
  have ha0 := substAt_scoped (church a) 0 (church b) (church_closed a)
  have h2 : Beta (.app (.abs (natPairExpr (church a) (.var 0))) (church b)) (natPairExpr (church a) (church b)) := by
    have h := Beta.contract (natPairExpr (church a) (.var 0)) (church b)
    rw [subst_natPairExpr] at h
    simpa [substAt, liftBy, ha0] using h
  let first : Term := .app (.app churchAdd (.app (.app churchMultiply (church b)) (church b))) (church a)
  let second : Term := .app (.app churchAdd
    (.app (.app churchAdd (.app (.app churchMultiply (church a)) (church a))) (church a))) (church b)
  have hfirst : Reaches first (church (b * b + a)) := by
    apply reaches_trans (reaches_appLeft (reaches_appRight churchAdd (churchMultiply_run b b)) (church a))
    exact churchAdd_run (b * b) a
  have hsecondInner : Reaches (.app (.app churchAdd (.app (.app churchMultiply (church a)) (church a))) (church a))
      (church (a * a + a)) := by
    apply reaches_trans (reaches_appLeft (reaches_appRight churchAdd (churchMultiply_run a a)) (church a))
    exact churchAdd_run (a * a) a
  have hsecond : Reaches second (church (a * a + a + b)) := by
    apply reaches_trans (reaches_appLeft (reaches_appRight churchAdd hsecondInner) (church b))
    exact churchAdd_run (a * a + a) b
  have hcond : Reaches (natPairExpr (church a) (church b))
      (.app (.app (if a < b then pairFirstSelector else pairSecondSelector) first) second) := by
    exact reaches_appLeft (reaches_appLeft (churchLess_run a b) first) second
  have hbranches : Reaches (.app (.app (if a < b then pairFirstSelector else pairSecondSelector) first) second)
      (.app (.app (if a < b then pairFirstSelector else pairSecondSelector) (church (b * b + a)))
        (church (a * a + a + b))) := by
    apply reaches_trans (reaches_appLeft (reaches_appRight _ hfirst) second)
    exact reaches_appRight _ hsecond
  have hselect : Reaches
      (.app (.app (if a < b then pairFirstSelector else pairSecondSelector) (church (b * b + a)))
        (church (a * a + a + b))) (church (Nat.pair a b)) := by
    by_cases h : a < b
    · simpa [h, Nat.pair] using pairFirstSelector_run (church_closed (b * b + a)) (church (a * a + a + b))
    · simpa [h, Nat.pair] using pairSecondSelector_run (church (b * b + a)) (church (a * a + a + b))
  exact .step (.appLeft h1) (.step h2 (reaches_trans hcond (reaches_trans hbranches hselect)))

theorem churchNatPair_represents : BinaryRepresents churchNatPair Nat.pair := by
  constructor
  · exact churchNatPair_closed
  · intro a b m
    constructor
    · intro h
      exact numeral_result_unique h (churchNatPair_run a b)
    · intro h
      subst m
      exact churchNatPair_run a b

#print axioms predecessorStep_run
#print axioms churchPredecessor_run
#print axioms churchPredecessor_represents
#print axioms churchSubtract_run
#print axioms churchSubtract_represents
#print axioms churchLess_run
#print axioms churchNatPair_run
#print axioms churchNatPair_represents

end LambdaTuring
