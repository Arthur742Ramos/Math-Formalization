/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.NumericalSemantics
public meta import LambdaTuring.NumericalSemantics

@[expose] public section

/-! Exhaustive finite exploration of full beta reduction. -/

namespace LambdaTuring

def rootReductions (f x : Term) : List Term :=
  match f with
  | .abs body => [substAt 0 x body]
  | _ => []

/-- All one-step full-beta reducts, including those below binders. -/
def betaSteps : Term → List Term
  | .var _ => []
  | .abs body => (betaSteps body).map Term.abs
  | .app f x => rootReductions f x ++
      (betaSteps f).map (fun g => .app g x) ++
      (betaSteps x).map (Term.app f)

theorem mem_rootReductions {f x r : Term} :
    r ∈ rootReductions f x ↔ ∃ body, f = .abs body ∧ r = substAt 0 x body := by
  cases f <;> simp [rootReductions, eq_comm]

theorem betaSteps_sound {t u : Term} (h : u ∈ betaSteps t) : Beta t u := by
  induction t generalizing u with
  | var i => simp [betaSteps] at h
  | abs body ih =>
    simp only [betaSteps, List.mem_map] at h
    obtain ⟨r, hr, rfl⟩ := h
    exact .abs (ih hr)
  | app f x ihf ihx =>
    simp only [betaSteps, List.mem_append, List.mem_map] at h
    rcases h with (h | h) | h
    · obtain ⟨body, rfl, rfl⟩ := mem_rootReductions.1 h
      exact .contract _ _
    · obtain ⟨r, hr, rfl⟩ := h
      exact .appLeft (ihf hr)
    · obtain ⟨r, hr, rfl⟩ := h
      exact .appRight (ihx hr)

theorem betaSteps_complete {t u : Term} (h : Beta t u) : u ∈ betaSteps t := by
  induction h with
  | contract body value => simp [betaSteps, rootReductions]
  | abs _ ih => simp [betaSteps, ih]
  | appLeft _ ih => simp [betaSteps, ih]
  | appRight _ ih => simp [betaSteps, ih]

theorem mem_betaSteps_iff {t u : Term} : u ∈ betaSteps t ↔ Beta t u :=
  ⟨betaSteps_sound, betaSteps_complete⟩

/-- Paths with at most `n` steps. -/
inductive BoundedReaches : Nat → Term → Term → Prop where
  | refl (n : Nat) (t : Term) : BoundedReaches n t t
  | step {n a b c} : Beta a b → BoundedReaches n b c → BoundedReaches (n + 1) a c

def explore : Nat → Term → List Term
  | 0, t => [t]
  | n + 1, t => t :: (betaSteps t).flatMap (explore n)

theorem mem_explore_iff (n : Nat) (t u : Term) : u ∈ explore n t ↔ BoundedReaches n t u := by
  induction n generalizing t with
  | zero =>
    constructor
    · simp [explore]; intro h; subst u; exact .refl _ _
    · intro h; cases h; simp [explore]
  | succ n ih =>
    constructor
    · simp only [explore, List.mem_cons, List.mem_flatMap, mem_betaSteps_iff, ih]
      rintro (rfl | ⟨b, hb, hc⟩)
      · exact .refl _ _
      · exact .step hb hc
    · intro h
      cases h with
      | refl => simp [explore]
      | step hb hc =>
        simp only [explore, List.mem_cons, List.mem_flatMap, mem_betaSteps_iff, ih]
        exact Or.inr ⟨_, hb, hc⟩

theorem bounded_to_reaches {n : Nat} {t u : Term} (h : BoundedReaches n t u) : Reaches t u := by
  induction h with
  | refl => exact .refl _
  | step h _ ih => exact .step h ih

theorem reaches_bounded {t u : Term} (h : Reaches t u) : ∃ n, BoundedReaches n t u := by
  induction h with
  | refl => exact ⟨0, .refl _ _⟩
  | step h _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step h hn⟩

theorem reaches_iff_explored (t u : Term) : Reaches t u ↔ ∃ n, u ∈ explore n t := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := reaches_bounded h
    exact ⟨n, (mem_explore_iff _ _ _).2 hn⟩
  · rintro ⟨n, hn⟩
    exact bounded_to_reaches ((mem_explore_iff _ _ _).1 hn)

#print axioms mem_betaSteps_iff
#print axioms reaches_iff_explored

end LambdaTuring
