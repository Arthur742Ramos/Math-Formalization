/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectBetaCode
public meta import LambdaTuring.DirectBetaCode

@[expose] public section

namespace LambdaTuring

/-- A finite sequence of paths certifies a sequence of full-beta contractions. -/
def betaRun : List (List Bool) → Term → Option Term
  | [], t => some t
  | path :: paths, t => (betaAtPath path t).bind (betaRun paths)

theorem betaRun_sound {paths : List (List Bool)} {t u : Term} (h : betaRun paths t = some u) :
    Reaches t u := by
  induction paths generalizing t with
  | nil =>
    simp [betaRun] at h
    subst u
    exact .refl _
  | cons path paths ih =>
    simp only [betaRun, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, hrest⟩ := h
    exact .step (betaAtPath_sound hv) (ih hrest)

theorem betaRun_complete {t u : Term} (h : Reaches t u) :
    ∃ paths, betaRun paths t = some u := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | step hs _ ih =>
    obtain ⟨path, hp⟩ := betaAtPath_complete hs
    obtain ⟨paths, hpaths⟩ := ih
    exact ⟨path :: paths, by simp [betaRun, hp, hpaths]⟩

theorem reaches_iff_betaRun (t u : Term) :
    Reaches t u ↔ ∃ paths, betaRun paths t = some u :=
  ⟨betaRun_complete, fun ⟨_, h⟩ => betaRun_sound h⟩

/-- A bounded state machine consumes one path per iteration and leaves an
    already exhausted path list unchanged. -/
def betaTrace : Nat → Option Term → List (List Bool) → Option Term × List (List Bool)
  | 0, current, paths => (current, paths)
  | fuel + 1, current, [] => betaTrace fuel current []
  | fuel + 1, current, path :: paths => betaTrace fuel (current.bind (betaAtPath path)) paths

theorem betaTrace_nil (fuel : Nat) (current : Option Term) :
    betaTrace fuel current [] = (current, []) := by
  induction fuel <;> simp [betaTrace, *]

theorem betaTrace_enough (fuel : Nat) (current : Option Term) (paths : List (List Bool))
    (h : paths.length ≤ fuel) :
    betaTrace fuel current paths = (current.bind (betaRun paths), []) := by
  induction fuel generalizing current paths with
  | zero =>
    cases paths with
    | nil => simp [betaTrace, betaRun]
    | cons path paths => simp at h
  | succ fuel ih =>
    cases paths with
    | nil => simp [betaTrace_nil, betaRun]
    | cons path paths =>
      have h' : paths.length ≤ fuel := by simp at h; omega
      rw [betaTrace, ih _ _ h']
      cases current <;> simp [betaRun]

theorem directPathList_length_le_code (paths : List (List Bool)) :
    paths.length ≤ Encodable.encode paths := by
  induction paths with
  | nil => simp
  | cons path paths ih =>
    rw [List.length_cons, Encodable.encode_list_cons]
    have h := Nat.right_le_pair (Encodable.encode path) (Encodable.encode paths)
    omega

theorem betaTrace_encoded_fuel (current : Option Term) (paths : List (List Bool)) :
    betaTrace (Encodable.encode paths) current paths = (current.bind (betaRun paths), []) :=
  betaTrace_enough _ _ _ (directPathList_length_le_code paths)

#print axioms reaches_iff_betaRun
#print axioms betaTrace_encoded_fuel
end LambdaTuring
