/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSRecursionState
public meta import LambdaTuring.CPSRecursionState

@[expose] public section

open Nat.Partrec

namespace LambdaTuring

/-- Abstract the fixed parameter over the recursion iterator.  The indices
    account for the binders inside both the state step and initial pair. -/
def cpsRecParameter (F G : Term) : Term :=
  .abs (.abs (.abs (.app (.app pairSecond
    (.app (.app (.var 1) (cpsRecStateStep G (.var 6)))
      (churchPair (church 0) (.app F (.var 3))))) (.var 0))))

theorem cpsRecParameter_closed {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) :
    Scoped 0 (cpsRecParameter F G) := by
  have hf4 := scoped_mono hf (Nat.zero_le 4)
  have hg7 := scoped_mono hg (Nat.zero_le 7)
  have hp7 := scoped_mono churchNatPair_closed (Nat.zero_le 7)
  have hq3 := scoped_mono pairSecond_closed (Nat.zero_le 3)
  have hq6 := scoped_mono pairSecond_closed (Nat.zero_le 6)
  have hr5 := scoped_mono pairFirst_closed (Nat.zero_le 5)
  have hr7 := scoped_mono pairFirst_closed (Nat.zero_le 7)
  have hu5 := scoped_mono churchSuccessor_closed (Nat.zero_le 5)
  have hz4 := scoped_mono (church_closed 0) (Nat.zero_le 4)
  simp [cpsRecParameter, cpsRecStateStep, churchPair, Scoped,
    hf4, hg7, hp7, hq3, hq6, hr5, hr7, hu5, hz4]

theorem cpsRecParameter_run {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) (a : Nat) :
    Reaches (.app (cpsRecParameter F G) (church a)) (cpsRecFixed F G (church a)) := by
  have hf3 := substAt_scoped F 3 (church a) (scoped_mono hf (Nat.zero_le 3))
  have hg6 := substAt_scoped G 6 (church a) (scoped_mono hg (Nat.zero_le 6))
  have hp6 := substAt_scoped churchNatPair 6 (church a) (scoped_mono churchNatPair_closed (Nat.zero_le 6))
  have hq2 := substAt_scoped pairSecond 2 (church a) (scoped_mono pairSecond_closed (Nat.zero_le 2))
  have hq5 := substAt_scoped pairSecond 5 (church a) (scoped_mono pairSecond_closed (Nat.zero_le 5))
  have hr4 := substAt_scoped pairFirst 4 (church a) (scoped_mono pairFirst_closed (Nat.zero_le 4))
  have hr6 := substAt_scoped pairFirst 6 (church a) (scoped_mono pairFirst_closed (Nat.zero_le 6))
  have hu4 := substAt_scoped churchSuccessor 4 (church a) (scoped_mono churchSuccessor_closed (Nat.zero_le 4))
  have hz3 := substAt_scoped (church 0) 3 (church a) (scoped_mono (church_closed 0) (Nat.zero_le 3))
  have ha3 := liftBy_closed 3 (church_closed a)
  have ha6 := liftBy_closed 6 (church_closed a)
  have hb : Beta (.app (cpsRecParameter F G) (church a)) (cpsRecFixed F G (church a)) := by
    simpa [cpsRecParameter, cpsRecFixed, cpsRecStateStep, churchPair, substAt,
      hf3, hg6, hp6, hq2, hq5, hr4, hr6, hu4, hz3, ha3, ha6] using
      (Beta.contract (.abs (.abs (.app (.app pairSecond
        (.app (.app (.var 1) (cpsRecStateStep G (.var 6)))
          (churchPair (church 0) (.app F (.var 3))))) (.var 0)))) (church a))
  exact .step hb (.refl _)

/-- Compile Mathlib's primitive recursion, using both projections of its
    encoded input. The step function receives `pair a (pair i previous)`. -/
def cpsRecursion (F G : Term) : Term :=
  .abs (.abs (.app (.app (.app (cpsRecParameter F G)
    (.app churchNumericLeft (.var 1))) (.app churchNumericRight (.var 1))) (.var 0)))

theorem cpsRecursion_closed {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) :
    Scoped 0 (cpsRecursion F G) := by
  have hp := scoped_mono (cpsRecParameter_closed hf hg) (Nat.zero_le 2)
  have hl := scoped_mono churchNumericLeft_closed (Nat.zero_le 2)
  have hr := scoped_mono churchNumericRight_closed (Nat.zero_le 2)
  simp [cpsRecursion, Scoped, hp, hl, hr]

theorem cpsRecursion_run {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) (x : Nat) (K : Term) :
    Reaches (.app (.app (cpsRecursion F G) (church x)) K)
      (.app (.app (cpsRecFixed F G (church x.unpair.1)) (church x.unpair.2)) K) := by
  let P := cpsRecParameter F G
  have hp : Scoped 0 P := cpsRecParameter_closed hf hg
  have hp1 := substAt_scoped P 1 (church x) (scoped_mono hp (Nat.zero_le 1))
  have hl1 := substAt_scoped churchNumericLeft 1 (church x) (scoped_mono churchNumericLeft_closed (Nat.zero_le 1))
  have hr1 := substAt_scoped churchNumericRight 1 (church x) (scoped_mono churchNumericRight_closed (Nat.zero_le 1))
  have hx1 := liftBy_closed 1 (church_closed x)
  have hb1 : Beta (.app (cpsRecursion F G) (church x))
      (.abs (.app (.app (.app P (.app churchNumericLeft (church x)))
        (.app churchNumericRight (church x))) (.var 0))) := by
    change Beta (.app (.abs (.abs (.app (.app (.app P (.app churchNumericLeft (.var 1)))
      (.app churchNumericRight (.var 1))) (.var 0)))) (church x)) _
    simpa [substAt, hp1, hl1, hr1, hx1] using
      (Beta.contract (.abs (.app (.app (.app P (.app churchNumericLeft (.var 1)))
        (.app churchNumericRight (.var 1))) (.var 0))) (church x))
  have hp0 := substAt_scoped P 0 K hp
  have hl0 := substAt_scoped churchNumericLeft 0 K churchNumericLeft_closed
  have hr0 := substAt_scoped churchNumericRight 0 K churchNumericRight_closed
  have hx0 := substAt_scoped (church x) 0 K (church_closed x)
  have hb2 : Beta (.app (.abs (.app (.app (.app P (.app churchNumericLeft (church x)))
      (.app churchNumericRight (church x))) (.var 0))) K)
      (.app (.app (.app P (.app churchNumericLeft (church x))) (.app churchNumericRight (church x))) K) := by
    simpa [substAt, liftBy, hp0, hl0, hr0, hx0] using
      (Beta.contract (.app (.app (.app P (.app churchNumericLeft (church x)))
        (.app churchNumericRight (church x))) (.var 0)) K)
  apply Reaches.step (.appLeft hb1)
  apply Reaches.step hb2
  have hleft := churchNumericLeft_run x
  have hright := churchNumericRight_run x
  have hpRun := cpsRecParameter_run hf hg x.unpair.1
  apply reaches_trans (reaches_appLeft (reaches_appLeft (reaches_appRight P hleft) _) K)
  apply reaches_trans (reaches_appLeft (reaches_appRight (.app P (church x.unpair.1)) hright) K)
  exact reaches_appLeft (reaches_appLeft hpRun (church x.unpair.2)) K

theorem cpsRecursion_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) :
    CPSRepresents (cpsRecursion F G)
      (fun x => partialRecUnroll f g x.unpair.1 x.unpair.2) := by
  constructor
  · exact cpsRecursion_closed hf.1 hg.1
  · intro x K
    have hp := cpsRecursion_run hf.1 hg.1 x K
    have ht := cpsRecFixed_represents hf hg x.unpair.1
    constructor
    · intro m hm
      exact reaches_trans hp ((ht.2 x.unpair.2 K).1 m hm)
    · intro hn
      exact noNormal_backward hp ((ht.2 x.unpair.2 K).2 hn)

theorem cpsRecursion_code {F G : Term} {f g : Nat.Partrec.Code}
    (hf : CPSRepresents F (Nat.Partrec.Code.eval f))
    (hg : CPSRepresents G (Nat.Partrec.Code.eval g)) :
    CPSRepresents (cpsRecursion F G) (Nat.Partrec.Code.eval (.prec f g)) := by
  have heq : (fun x => partialRecUnroll (Nat.Partrec.Code.eval f) (Nat.Partrec.Code.eval g)
      x.unpair.1 x.unpair.2) = Nat.Partrec.Code.eval (.prec f g) := by
    funext x
    rw [partialRecUnroll_code, Nat.pair_unpair]
  rw [← heq]
  exact cpsRecursion_represents hf hg

theorem primrec_cpsRecursion : Primrec₂ cpsRecursion := by
  change Primrec (fun p : Term × Term => cpsRecursion p.1 p.2)
  unfold cpsRecursion cpsRecParameter cpsRecStateStep churchPair
  repeat' first | exact Primrec.fst | exact Primrec.snd | exact Primrec.const _ |
    apply primrec_abs.comp | apply primrec_app.comp

#print axioms cpsRecParameter_run
#print axioms cpsRecursion_code
#print axioms primrec_cpsRecursion

end LambdaTuring
