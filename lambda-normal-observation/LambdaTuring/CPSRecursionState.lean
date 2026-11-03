/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.CPSRecursionUnroll
public meta import LambdaTuring.CPSRecursionUnroll
public import LambdaTuring.ChurchUnpair
public meta import LambdaTuring.ChurchUnpair

@[expose] public section

/- The indexed Church-pair state follows Isabelle's
   Lambda_CPS_Primitive_State, with Mathlib numeric pairing in the step. -/

namespace LambdaTuring

/-- A nullary CPS step with a closed fixed first argument and index. -/
def cpsRecThunkStep (G A : Term) (i : Nat) (C : Term) : Term :=
  .abs (.app C (.abs (.app (.app G
    (.app (.app churchNatPair A) (.app (.app churchNatPair (church i)) (.var 0)))) (.var 1))))

/-- State is a Church pair of the current index and its nullary CPS result. -/
def cpsRecStateStep (G A : Term) : Term :=
  .abs (.abs (.app
    (.app (.var 0) (.app churchSuccessor (.app pairFirst (.var 1))))
    (.abs (.app (.app pairSecond (.var 2))
      (.abs (.app (.app G (.app (.app churchNatPair A)
        (.app (.app churchNatPair (.app pairFirst (.var 3))) (.var 0)))) (.var 1)))))))

theorem cpsRecThunkStep_closed {G A C : Term}
    (hg : Scoped 0 G) (ha : Scoped 0 A) (hc : Scoped 0 C) (i : Nat) :
    Scoped 0 (cpsRecThunkStep G A i C) := by
  have hg2 := scoped_mono hg (Nat.zero_le 2)
  have ha2 := scoped_mono ha (Nat.zero_le 2)
  have hc1 := scoped_mono hc (Nat.zero_le 1)
  have hp2 := scoped_mono churchNatPair_closed (Nat.zero_le 2)
  have hi2 := scoped_mono (church_closed i) (Nat.zero_le 2)
  simp [cpsRecThunkStep, Scoped, hg2, ha2, hc1, hp2, hi2]

theorem cpsRecStateStep_closed {G A : Term} (hg : Scoped 0 G) (ha : Scoped 0 A) :
    Scoped 0 (cpsRecStateStep G A) := by
  have hg4 := scoped_mono hg (Nat.zero_le 4)
  have ha4 := scoped_mono ha (Nat.zero_le 4)
  have hp4 := scoped_mono churchNatPair_closed (Nat.zero_le 4)
  have hf2 := scoped_mono pairFirst_closed (Nat.zero_le 2)
  have hf4 := scoped_mono pairFirst_closed (Nat.zero_le 4)
  have hs3 := scoped_mono pairSecond_closed (Nat.zero_le 3)
  have hu2 := scoped_mono churchSuccessor_closed (Nat.zero_le 2)
  simp [cpsRecStateStep, Scoped, hg4, ha4, hp4, hf2, hf4, hs3, hu2]

theorem cpsRecStateStep_run {G A C : Term} (hg : Scoped 0 G) (ha : Scoped 0 A)
    (hc : Scoped 0 C) (i : Nat) :
    Reaches (.app (cpsRecStateStep G A) (churchPair (church i) C))
      (churchPair (church (i + 1)) (cpsRecThunkStep G A i C)) := by
  let P := churchPair (church i) C
  have hP : Scoped 0 P := churchPair_closed (church_closed i) hc
  have hfirst : Reaches (.app pairFirst P) (church i) := pairFirst_run (church_closed i) hc
  have hsecond : Reaches (.app pairSecond P) C := pairSecond_run (church_closed i) hc
  have hindex : Reaches (.app churchSuccessor (.app pairFirst P)) (church (i + 1)) :=
    reaches_trans (reaches_appRight churchSuccessor hfirst) (churchSuccessor_run i)
  have hg3 := substAt_scoped G 3 P (scoped_mono hg (Nat.zero_le 3))
  have ha3 := substAt_scoped A 3 P (scoped_mono ha (Nat.zero_le 3))
  have hp3 := substAt_scoped churchNatPair 3 P (scoped_mono churchNatPair_closed (Nat.zero_le 3))
  have hf3 := substAt_scoped pairFirst 3 P (scoped_mono pairFirst_closed (Nat.zero_le 3))
  have hf1 := substAt_scoped pairFirst 1 P (scoped_mono pairFirst_closed (Nat.zero_le 1))
  have hs2 := substAt_scoped pairSecond 2 P (scoped_mono pairSecond_closed (Nat.zero_le 2))
  have hu1 := substAt_scoped churchSuccessor 1 P (scoped_mono churchSuccessor_closed (Nat.zero_le 1))
  have hP1 := liftBy_closed 1 hP
  have hP2 := liftBy_closed 2 hP
  have hP3 := liftBy_closed 3 hP
  have hb : Beta (.app (cpsRecStateStep G A) P)
      (.abs (.app (.app (.var 0) (.app churchSuccessor (.app pairFirst P)))
        (.abs (.app (.app pairSecond P)
          (.abs (.app (.app G (.app (.app churchNatPair A)
            (.app (.app churchNatPair (.app pairFirst P)) (.var 0)))) (.var 1))))))) := by
    simpa [cpsRecStateStep, substAt, hg3, ha3, hp3, hf3, hf1, hs2, hu1, hP1, hP2, hP3] using
      (Beta.contract (.abs (.app
        (.app (.var 0) (.app churchSuccessor (.app pairFirst (.var 1))))
        (.abs (.app (.app pairSecond (.var 2))
          (.abs (.app (.app G (.app (.app churchNatPair A)
            (.app (.app churchNatPair (.app pairFirst (.var 3))) (.var 0)))) (.var 1))))))) P)
  apply Reaches.step hb
  unfold churchPair cpsRecThunkStep
  repeat' first | exact hindex | exact hfirst | exact hsecond | exact Reaches.refl _ |
    apply reaches_abs | apply reaches_app_both

def CPSNullaryRepresents (C : Term) (p : Part Nat) : Prop :=
  Scoped 0 C ∧ ∀ K,
    (∀ m, m ∈ p → Reaches (.app C K) (.app K (church m))) ∧
    (p = Part.none → ¬ ∃ N, Reaches (.app C K) N ∧ ¬ ∃ u, Beta N u)

def cpsRecThunkCont (G : Term) (a i : Nat) (K : Term) : Term :=
  .abs (.app (.app G (.app (.app churchNatPair (church a))
    (.app (.app churchNatPair (church i)) (.var 0)))) (liftFrom 0 K))

theorem cpsRecThunkStep_run {G C : Term} (hg : Scoped 0 G) (hc : Scoped 0 C)
    (a i : Nat) (K : Term) :
    Reaches (.app (cpsRecThunkStep G (church a) i C) K)
      (.app C (cpsRecThunkCont G a i K)) := by
  have hc0 := substAt_scoped C 0 K hc
  have hg1 := substAt_scoped G 1 K (scoped_mono hg (Nat.zero_le 1))
  have hp1 := substAt_scoped churchNatPair 1 K (scoped_mono churchNatPair_closed (Nat.zero_le 1))
  have ha1 := substAt_scoped (church a) 1 K (scoped_mono (church_closed a) (Nat.zero_le 1))
  have hi1 := substAt_scoped (church i) 1 K (scoped_mono (church_closed i) (Nat.zero_le 1))
  have hb : Beta (.app (cpsRecThunkStep G (church a) i C) K)
      (.app C (cpsRecThunkCont G a i K)) := by
    simpa [cpsRecThunkStep, cpsRecThunkCont, substAt, liftBy, hc0, hg1, hp1, ha1, hi1] using
      (Beta.contract (.app C (.abs (.app (.app G
        (.app (.app churchNatPair (church a)) (.app (.app churchNatPair (church i)) (.var 0)))) (.var 1)))) K)
  exact .step hb (.refl _)

theorem cpsRecThunkCont_run {G : Term} (hg : Scoped 0 G) (a i v : Nat) (K : Term) :
    Reaches (.app (cpsRecThunkCont G a i K) (church v))
      (.app (.app G (church (Nat.pair a (Nat.pair i v)))) K) := by
  have hg0 := substAt_scoped G 0 (church v) hg
  have hp0 := substAt_scoped churchNatPair 0 (church v) churchNatPair_closed
  have ha0 := substAt_scoped (church a) 0 (church v) (church_closed a)
  have hi0 := substAt_scoped (church i) 0 (church v) (church_closed i)
  have hk := substAt_liftFrom K 0 (church v)
  have hb : Beta (.app (cpsRecThunkCont G a i K) (church v))
      (.app (.app G (.app (.app churchNatPair (church a))
        (.app (.app churchNatPair (church i)) (church v)))) K) := by
    simpa [cpsRecThunkCont, substAt, liftBy, hg0, hp0, ha0, hi0, hk] using
      (Beta.contract (.app (.app G (.app (.app churchNatPair (church a))
        (.app (.app churchNatPair (church i)) (.var 0)))) (liftFrom 0 K)) (church v))
  apply Reaches.step hb
  apply reaches_appLeft (reaches_appRight G ?_) K
  apply reaches_trans (reaches_appRight (.app churchNatPair (church a)) (churchNatPair_run i v))
  exact churchNatPair_run a (Nat.pair i v)

theorem cpsRecThunkStep_represents {G C : Term} {g : Nat →. Nat} {p : Part Nat}
    (hg : CPSRepresents G g) (hc : CPSNullaryRepresents C p) (a i : Nat) :
    CPSNullaryRepresents (cpsRecThunkStep G (church a) i C)
      (p.bind (fun v => g (Nat.pair a (Nat.pair i v)))) := by
  constructor
  · exact cpsRecThunkStep_closed hg.1 (church_closed a) hc.1 i
  · intro K
    have hprefix := cpsRecThunkStep_run hg.1 hc.1 a i K
    have hnext : ∀ v, v ∈ p → Reaches (.app (cpsRecThunkStep G (church a) i C) K)
        (.app (.app G (church (Nat.pair a (Nat.pair i v)))) K) := by
      intro v hv
      exact reaches_trans hprefix
        (reaches_trans ((hc.2 (cpsRecThunkCont G a i K)).1 v hv) (cpsRecThunkCont_run hg.1 a i v K))
    constructor
    · intro m hm
      obtain ⟨v, hv, hm⟩ := Part.mem_bind_iff.1 hm
      exact reaches_trans (hnext v hv) ((hg.2 _ K).1 m hm)
    · intro hnone
      by_cases hd : p.Dom
      · obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hd
        have hgNone : g (Nat.pair a (Nat.pair i v)) = Part.none := by
          apply Part.eq_none_iff.2
          intro m hm
          have hx : m ∈ p.bind (fun v => g (Nat.pair a (Nat.pair i v))) :=
            Part.mem_bind_iff.2 ⟨v, hv, hm⟩
          rw [hnone] at hx
          simp at hx
        exact noNormal_backward (hnext v hv) ((hg.2 _ K).2 hgNone)
      · have hpNone : p = Part.none := by
          apply Part.eq_none_iff.2
          intro m hm
          exact hd (Part.dom_iff_mem.2 ⟨m, hm⟩)
        exact noNormal_backward hprefix ((hc.2 (cpsRecThunkCont G a i K)).2 hpNone)

def cpsRecThunkUnroll (F G : Term) (a : Nat) : Nat → Term
  | 0 => .app F (church a)
  | i + 1 => cpsRecThunkStep G (church a) i (cpsRecThunkUnroll F G a i)

theorem cpsRecThunkUnroll_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) (a n : Nat) :
    CPSNullaryRepresents (cpsRecThunkUnroll F G a n) (partialRecUnroll f g a n) := by
  induction n with
  | zero =>
    constructor
    · exact ⟨hf.1, church_closed a⟩
    · exact hf.2 a
  | succ n ih => exact cpsRecThunkStep_represents hg ih a n

theorem cpsRecState_iteration {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G)
    (a n : Nat) :
    Reaches (churchIter n (cpsRecStateStep G (church a)) (churchPair (church 0) (.app F (church a))))
      (churchPair (church n) (cpsRecThunkUnroll F G a n)) := by
  have hunroll : ∀ n, Scoped 0 (cpsRecThunkUnroll F G a n) := by
    intro n
    induction n with
    | zero => exact ⟨hf, church_closed a⟩
    | succ n ih => exact cpsRecThunkStep_closed hg (church_closed a) ih n
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    exact reaches_trans (reaches_appRight (cpsRecStateStep G (church a)) ih)
      (cpsRecStateStep_run hg (church_closed a) (hunroll n) n)

/-- A uniform lambda iterator for a fixed closed first argument. -/
def cpsRecFixed (F G A : Term) : Term :=
  .abs (.abs (.app (.app pairSecond
    (.app (.app (.var 1) (cpsRecStateStep G A)) (churchPair (church 0) (.app F A)))) (.var 0)))

theorem cpsRecFixed_closed {F G A : Term} (hf : Scoped 0 F) (hg : Scoped 0 G) (ha : Scoped 0 A) :
    Scoped 0 (cpsRecFixed F G A) := by
  have hs := scoped_mono (cpsRecStateStep_closed hg ha) (Nat.zero_le 2)
  have hb : Scoped 0 (churchPair (church 0) (.app F A)) :=
    churchPair_closed (church_closed 0) ⟨hf, ha⟩
  have hb2 := scoped_mono hb (Nat.zero_le 2)
  have hp := scoped_mono pairSecond_closed (Nat.zero_le 2)
  simp [cpsRecFixed, Scoped, hs, hb2, hp]

theorem cpsRecFixed_run {F G : Term} (hf : Scoped 0 F) (hg : Scoped 0 G)
    (a n : Nat) (K : Term) :
    Reaches (.app (.app (cpsRecFixed F G (church a)) (church n)) K)
      (.app (cpsRecThunkUnroll F G a n) K) := by
  let S := cpsRecStateStep G (church a)
  let P := churchPair (church 0) (.app F (church a))
  have hS : Scoped 0 S := cpsRecStateStep_closed hg (church_closed a)
  have hP : Scoped 0 P := churchPair_closed (church_closed 0) ⟨hf, church_closed a⟩
  have hu_all : ∀ j, Scoped 0 (cpsRecThunkUnroll F G a j) := by
    intro j
    induction j with
    | zero => exact ⟨hf, church_closed a⟩
    | succ j ih => exact cpsRecThunkStep_closed hg (church_closed a) ih j
  have hs1 := substAt_scoped S 1 (church n) (scoped_mono hS (Nat.zero_le 1))
  have hp1 := substAt_scoped P 1 (church n) (scoped_mono hP (Nat.zero_le 1))
  have hq1 := substAt_scoped pairSecond 1 (church n) (scoped_mono pairSecond_closed (Nat.zero_le 1))
  have hn1 := liftBy_closed 1 (church_closed n)
  have hb1 : Beta (.app (cpsRecFixed F G (church a)) (church n))
      (.abs (.app (.app pairSecond (.app (.app (church n) S) P)) (.var 0))) := by
    change Beta (.app (.abs (.abs (.app (.app pairSecond (.app (.app (.var 1) S) P)) (.var 0)))) (church n)) _
    simpa [substAt, hs1, hp1, hq1, hn1] using
      (Beta.contract (.abs (.app (.app pairSecond (.app (.app (.var 1) S) P)) (.var 0))) (church n))
  have hs0 := substAt_scoped S 0 K hS
  have hp0 := substAt_scoped P 0 K hP
  have hq0 := substAt_scoped pairSecond 0 K pairSecond_closed
  have hn0 := substAt_scoped (church n) 0 K (church_closed n)
  have hb2 : Beta (.app (.abs (.app (.app pairSecond (.app (.app (church n) S) P)) (.var 0))) K)
      (.app (.app pairSecond (.app (.app (church n) S) P)) K) := by
    simpa [substAt, liftBy, hs0, hp0, hq0, hn0] using
      (Beta.contract (.app (.app pairSecond (.app (.app (church n) S) P)) (.var 0)) K)
  have hi : Reaches (.app (.app (church n) S) P)
      (churchPair (church n) (cpsRecThunkUnroll F G a n)) :=
    reaches_trans (church_iterates n S P) (cpsRecState_iteration hf hg a n)
  have hproject : Reaches (.app pairSecond (.app (.app (church n) S) P)) (cpsRecThunkUnroll F G a n) :=
    reaches_trans (reaches_appRight pairSecond hi) (pairSecond_run (church_closed n) (hu_all n))
  exact .step (.appLeft hb1) (.step hb2 (reaches_appLeft hproject K))

theorem cpsRecFixed_represents {F G : Term} {f g : Nat →. Nat}
    (hf : CPSRepresents F f) (hg : CPSRepresents G g) (a : Nat) :
    CPSRepresents (cpsRecFixed F G (church a)) (fun n => partialRecUnroll f g a n) := by
  constructor
  · exact cpsRecFixed_closed hf.1 hg.1 (church_closed a)
  · intro n K
    have hprefix := cpsRecFixed_run hf.1 hg.1 a n K
    have ht := cpsRecThunkUnroll_represents hf hg a n
    constructor
    · intro m hm
      exact reaches_trans hprefix ((ht.2 K).1 m hm)
    · intro hnone
      exact noNormal_backward hprefix ((ht.2 K).2 hnone)

#print axioms cpsRecStateStep_run
#print axioms cpsRecThunkUnroll_represents
#print axioms cpsRecState_iteration
#print axioms cpsRecFixed_represents

end LambdaTuring
