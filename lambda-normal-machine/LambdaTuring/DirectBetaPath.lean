/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectSubstCode
public meta import LambdaTuring.DirectSubstCode

@[expose] public section

namespace LambdaTuring

/-- A finite path selects a root contraction, an abstraction body, or either
    application branch. Invalid paths produce no term. -/
def betaAtPath : List Bool → Term → Option Term
  | [], .app (.abs body) value => some (substAt 0 value body)
  | false :: path, .abs body => (betaAtPath path body).map Term.abs
  | false :: path, .app f x => (betaAtPath path f).map (fun g => .app g x)
  | true :: path, .app f x => (betaAtPath path x).map (Term.app f)
  | _, _ => none

theorem betaAtPath_sound {path : List Bool} {t u : Term} (h : betaAtPath path t = some u) : Beta t u := by
  induction path generalizing t u with
  | nil =>
    cases t with
    | var n => simp [betaAtPath] at h
    | abs body => simp [betaAtPath] at h
    | app f x =>
      cases f with
      | var n => simp [betaAtPath] at h
      | app g y => simp [betaAtPath] at h
      | abs body =>
        simp [betaAtPath] at h
        subst u
        exact .contract body x
  | cons bit path ih =>
    cases bit with
    | false =>
      cases t with
      | var n => simp [betaAtPath] at h
      | abs body =>
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .abs (ih hv)
      | app f x =>
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .appLeft (ih hv)
    | true =>
      cases t with
      | var n => simp [betaAtPath] at h
      | abs body => simp [betaAtPath] at h
      | app f x =>
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
        exact .appRight (ih hv)

theorem betaAtPath_complete {t u : Term} (h : Beta t u) : ∃ path, betaAtPath path t = some u := by
  induction h with
  | contract body value => exact ⟨[], rfl⟩
  | abs _ ih =>
    obtain ⟨path, hp⟩ := ih
    exact ⟨false :: path, by simp [betaAtPath, hp]⟩
  | appLeft _ ih =>
    obtain ⟨path, hp⟩ := ih
    exact ⟨false :: path, by simp [betaAtPath, hp]⟩
  | appRight _ ih =>
    obtain ⟨path, hp⟩ := ih
    exact ⟨true :: path, by simp [betaAtPath, hp]⟩

theorem beta_iff_exists_path (t u : Term) : Beta t u ↔ ∃ path, betaAtPath path t = some u := by
  constructor
  · exact betaAtPath_complete
  · rintro ⟨path, h⟩
    exact betaAtPath_sound h

#print axioms betaAtPath
#print axioms beta_iff_exists_path
end LambdaTuring
