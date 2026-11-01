/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.Machine
public meta import LambdaTuring.Machine

@[expose] public section

namespace LambdaTuring.Machine

/-- Return the terminal configuration if it is reached within the step bound. -/
def haltWithin {states : Nat} (p : Program states) : Nat → Config states → Option (Config states)
  | 0, c => if step p c = none then some c else none
  | fuel + 1, c => match step p c with
    | none => some c
    | some next => haltWithin p fuel next

theorem haltWithin_sound {states : Nat} (p : Program states) (fuel : Nat)
    (start terminal : Config states) (h : haltWithin p fuel start = some terminal) :
    Reaches p start terminal ∧ Halted p terminal := by
  induction fuel generalizing start with
  | zero =>
    by_cases hs : step p start = none
    · simp [haltWithin, hs] at h
      subst terminal
      exact ⟨.refl _, hs⟩
    · simp [haltWithin, hs] at h
  | succ fuel ih =>
    cases hs : step p start with
    | none =>
      simp [haltWithin, hs] at h
      subst terminal
      exact ⟨.refl _, hs⟩
    | some next =>
      have hr : haltWithin p fuel next = some terminal := by simpa [haltWithin, hs] using h
      obtain ⟨reach, halt⟩ := ih next hr
      exact ⟨.step hs reach, halt⟩

theorem haltWithin_complete {states : Nat} {p : Program states} {start terminal : Config states}
    (h : Reaches p start terminal) (ht : Halted p terminal) :
    ∃ fuel, haltWithin p fuel start = some terminal := by
  induction h with
  | refl => exact ⟨0, by simp [haltWithin, Halted] at ht ⊢; exact ht⟩
  | step hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih ht
    exact ⟨fuel + 1, by simp [haltWithin, hs, hf]⟩

/-- A malformed halt has no numerical observation at any bound. -/
def observeWithin {states : Nat} (p : Program states) (n fuel : Nat) : Option Nat :=
  (haltWithin p fuel (initial n)).bind fun c => decode (c.tape.head :: c.tape.right)

theorem yields_iff_observeWithin {states : Nat} (p : Program states) (n m : Nat) :
    Yields p n m ↔ ∃ fuel, observeWithin p n fuel = some m := by
  constructor
  · rintro ⟨c, hr, hh, hd⟩
    obtain ⟨fuel, hf⟩ := haltWithin_complete hr hh
    exact ⟨fuel, by simp [observeWithin, hf, hd]⟩
  · rintro ⟨fuel, hf⟩
    cases hc : haltWithin p fuel (initial n) with
    | none => simp [observeWithin, hc] at hf
    | some c =>
      have hd : decode (c.tape.head :: c.tape.right) = some m := by
        simpa [observeWithin, hc] using hf
      obtain ⟨hr, hh⟩ := haltWithin_sound p fuel _ c hc
      exact ⟨c, hr, hh, hd⟩

#print axioms yields_iff_observeWithin

end LambdaTuring.Machine
