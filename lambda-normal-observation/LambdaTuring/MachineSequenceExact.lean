/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.MachineSequence
public meta import LambdaTuring.MachineSequence

@[expose] public section

namespace LambdaTuring.Machine

/-- In a deterministic machine, a terminal run extends every other finite
run from the same starting configuration. -/
theorem reaches_prefix_of_terminal {states : Nat} {p : Program states} {a b c : Config states}
    (hab : Reaches p a b) (hac : Reaches p a c) (hc : Halted p c) : Reaches p b c := by
  induction hab generalizing c with
  | refl => exact hac
  | @step a next b hs hr ih =>
    cases hac with
    | refl =>
      change step p a = none at hc
      rw [hc] at hs
      cases hs
    | @step _ next' c hs' hr' =>
      have he : next = next' := Option.some.inj (hs.symm.trans hs')
      subst next'
      exact ih hr' hc

theorem sequence_right_reflect {n m : Nat} (a : Program n) (b : Program m)
    (x y : Config (n + m + 1)) (h : Reaches (sequenceProgram a b) x y) :
    ∀ c : Config m, x = sequenceRightConfig c →
      ∃ d : Config m, y = sequenceRightConfig d ∧ Reaches b c d := by
  induction h with
  | refl =>
    intro c hc
    exact ⟨c, hc, .refl _⟩
  | @step x next y hs hr ih =>
    intro c hc
    subst x
    rw [sequence_right_step] at hs
    cases hs' : step b c with
    | none => simp [hs'] at hs
    | some d =>
      simp only [hs', Option.map_some, Option.some.injEq] at hs
      subst next
      obtain ⟨e, he, hde⟩ := ih d rfl
      exact ⟨e, he, .step hs' hde⟩

theorem sequence_right_halt_iff {n m : Nat} (a : Program n) (b : Program m) (c : Config m) :
    Halted (sequenceProgram a b) (sequenceRightConfig c) ↔ Halted b c := by
  change step (sequenceProgram a b) (sequenceRightConfig c) = none ↔ step b c = none
  rw [sequence_right_step]
  cases step b c <;> simp

/-- Once the first stage is known to terminate, terminal configurations of
the sequence are exactly the terminal configurations of the second stage.
No numerical-decoder condition is imposed. -/
theorem sequence_terminal_iff {n m : Nat} (a : Program n) (b : Program m)
    (start mid : Config n) (hfirst : Reaches a start mid) (hhalt : Halted a mid)
    (z : Config (n + m + 1)) :
    (Reaches (sequenceProgram a b) (sequenceLeftConfig start) z ∧ Halted (sequenceProgram a b) z) ↔
      ∃ d : Config m, z = sequenceRightConfig d ∧
        Reaches b ⟨⟨0, Nat.zero_lt_succ m⟩, mid.tape⟩ d ∧ Halted b d := by
  let secondStart : Config m := ⟨⟨0, Nat.zero_lt_succ m⟩, mid.tape⟩
  have hpref : Reaches (sequenceProgram a b) (sequenceLeftConfig start)
      (sequenceRightConfig secondStart) := by
    apply reaches_trans (sequence_left_reaches a b start mid hfirst)
    exact .step (sequence_switch a b mid hhalt) (.refl _)
  constructor
  · rintro ⟨hz, hzhalt⟩
    have htail := reaches_prefix_of_terminal hpref hz hzhalt
    obtain ⟨d, rfl, hd⟩ := sequence_right_reflect a b _ _ htail secondStart rfl
    exact ⟨d, rfl, hd, (sequence_right_halt_iff a b d).1 hzhalt⟩
  · rintro ⟨d, rfl, hd, hdh⟩
    exact ⟨reaches_trans hpref (sequence_right_reaches a b _ _ hd), sequence_right_halts a b d hdh⟩

/-- Any tape observation, including rejection of malformed halts, is
preserved exactly after a terminating first stage. -/
theorem sequence_observation_iff {n m : Nat} (a : Program n) (b : Program m)
    (start mid : Config n) (hfirst : Reaches a start mid) (hhalt : Halted a mid)
    (obs : Tape → Option Nat) (value : Nat) :
    (∃ z, Reaches (sequenceProgram a b) (sequenceLeftConfig start) z ∧
      Halted (sequenceProgram a b) z ∧ obs z.tape = some value) ↔
    (∃ d, Reaches b ⟨⟨0, Nat.zero_lt_succ m⟩, mid.tape⟩ d ∧ Halted b d ∧ obs d.tape = some value) := by
  constructor
  · rintro ⟨z, hr, hh, ho⟩
    obtain ⟨d, rfl, hd, hdh⟩ := (sequence_terminal_iff a b start mid hfirst hhalt z).1 ⟨hr, hh⟩
    exact ⟨d, hd, hdh, ho⟩
  · rintro ⟨d, hd, hdh, ho⟩
    refine ⟨sequenceRightConfig d, ?_, ?_, ho⟩
    exacts [((sequence_terminal_iff a b start mid hfirst hhalt _).2 ⟨d, rfl, hd, hdh⟩).1,
      ((sequence_terminal_iff a b start mid hfirst hhalt _).2 ⟨d, rfl, hd, hdh⟩).2]

theorem sequence_no_observation_iff {n m : Nat} (a : Program n) (b : Program m)
    (start mid : Config n) (hfirst : Reaches a start mid) (hhalt : Halted a mid)
    (obs : Tape → Option Nat) :
    (¬ ∃ value z, Reaches (sequenceProgram a b) (sequenceLeftConfig start) z ∧
      Halted (sequenceProgram a b) z ∧ obs z.tape = some value) ↔
    (¬ ∃ value d, Reaches b ⟨⟨0, Nat.zero_lt_succ m⟩, mid.tape⟩ d ∧
      Halted b d ∧ obs d.tape = some value) := by
  constructor
  · rintro h ⟨value, d, hd, hh, ho⟩
    obtain ⟨z, hz, hzh, hzo⟩ := (sequence_observation_iff a b start mid hfirst hhalt obs value).2
      ⟨d, hd, hh, ho⟩
    exact h ⟨value, z, hz, hzh, hzo⟩
  · rintro h ⟨value, z, hz, hh, ho⟩
    obtain ⟨d, hd, hdh, hdo⟩ := (sequence_observation_iff a b start mid hfirst hhalt obs value).1
      ⟨z, hz, hh, ho⟩
    exact h ⟨value, d, hd, hdh, hdo⟩

#print axioms sequence_terminal_iff
#print axioms sequence_observation_iff
#print axioms sequence_no_observation_iff
end LambdaTuring.Machine
