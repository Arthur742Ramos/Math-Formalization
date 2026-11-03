/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.DirectCourseCode
public meta import LambdaTuring.DirectCourseCode

@[expose] public section

namespace LambdaTuring

/-- Every variable index occurring in the term is below a common bound. -/
def IndicesBelow (bound : Nat) : Term → Prop
  | .var n => n < bound
  | .abs t => IndicesBelow bound t
  | .app f x => IndicesBelow bound f ∧ IndicesBelow bound x

theorem indicesBelow_mono {a b : Nat} (h : a ≤ b) (t : Term) :
    IndicesBelow a t → IndicesBelow b t := by
  induction t with
  | var n => exact fun hn => lt_of_lt_of_le hn h
  | abs t ih => exact ih
  | app f x ihf ihx => exact fun ⟨hf, hx⟩ => ⟨ihf hf, ihx hx⟩

theorem indicesBelow_directTermNumber (t : Term) : IndicesBelow (directTermNumber t) t := by
  induction t with
  | var n =>
    have h := Nat.right_le_pair 0 n
    simp only [IndicesBelow, directTermNumber]
    omega
  | abs t ih =>
    exact indicesBelow_mono (Nat.le_of_lt (directTermNumber_abs_lt t)) t ih
  | app f x ihf ihx =>
    exact ⟨indicesBelow_mono (Nat.le_of_lt (directTermNumber_app_left_lt f x)) f ihf,
      indicesBelow_mono (Nat.le_of_lt (directTermNumber_app_right_lt f x)) x ihx⟩

theorem liftFrom_eq_self_of_indicesBelow (t : Term) (cutoff : Nat) :
    IndicesBelow cutoff t → liftFrom cutoff t = t := by
  induction t generalizing cutoff with
  | var n =>
    intro h
    simp [liftFrom, IndicesBelow] at h ⊢
    exact h
  | abs t ih =>
    intro h
    simp only [liftFrom, Term.abs.injEq]
    exact ih (cutoff + 1) (indicesBelow_mono (by omega) t h)
  | app f x ihf ihx =>
    rintro ⟨hf, hx⟩
    simp only [liftFrom, Term.app.injEq]
    exact ⟨ihf cutoff hf, ihx cutoff hx⟩

theorem substAt_eq_self_of_indicesBelow (t : Term) (depth : Nat) (value : Term) :
    IndicesBelow depth t → substAt depth value t = t := by
  induction t generalizing depth with
  | var n =>
    intro h
    have hn : n < depth := h
    simp [substAt, Nat.ne_of_lt hn, Nat.not_lt_of_ge (Nat.le_of_lt hn)]
  | abs t ih =>
    intro h
    simp only [substAt, Term.abs.injEq]
    exact ih (depth + 1) (indicesBelow_mono (by omega) t h)
  | app f x ihf ihx =>
    rintro ⟨hf, hx⟩
    simp only [substAt, Term.app.injEq]
    exact ⟨ihf depth hf, ihx depth hx⟩

theorem liftFrom_eq_self_of_code_le (t : Term) (cutoff : Nat) (h : directTermNumber t ≤ cutoff) :
    liftFrom cutoff t = t :=
  liftFrom_eq_self_of_indicesBelow t cutoff (indicesBelow_mono h t (indicesBelow_directTermNumber t))

theorem substAt_eq_self_of_code_le (t : Term) (depth : Nat) (value : Term)
    (h : directTermNumber t ≤ depth) : substAt depth value t = t :=
  substAt_eq_self_of_indicesBelow t depth value (indicesBelow_mono h t (indicesBelow_directTermNumber t))

theorem directAppKey_left_lt (f x : Term) (depth : Nat) :
    Nat.pair (directTermNumber f) depth < Nat.pair (directTermNumber (.app f x)) depth :=
  Nat.pair_lt_pair_left depth (directTermNumber_app_left_lt f x)

theorem directAppKey_right_lt (f x : Term) (depth : Nat) :
    Nat.pair (directTermNumber x) depth < Nat.pair (directTermNumber (.app f x)) depth :=
  Nat.pair_lt_pair_left depth (directTermNumber_app_right_lt f x)

theorem directAbsKey_lt (t : Term) (depth : Nat) (hactive : depth + 1 < directTermNumber t) :
    Nat.pair (directTermNumber t) (depth + 1) < Nat.pair (directTermNumber (.abs t)) depth := by
  have hchild := directTermNumber_abs_lt t
  have h₁ : Nat.pair (directTermNumber t) (depth + 1) < (directTermNumber t + 1) ^ 2 := by
    simpa [Nat.max_eq_left (Nat.le_of_lt hactive)] using Nat.pair_lt_max_add_one_sq (directTermNumber t) (depth + 1)
  have h₂ : (directTermNumber t + 1) ^ 2 ≤ directTermNumber (.abs t) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have h₃ : directTermNumber (.abs t) ^ 2 ≤ Nat.pair (directTermNumber (.abs t)) depth := by
    have hp := Nat.max_sq_add_min_le_pair (directTermNumber (.abs t)) depth
    have hm : directTermNumber (.abs t) ^ 2 ≤ (max (directTermNumber (.abs t)) depth) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_max_left _ _) 2
    omega
  exact lt_of_lt_of_le h₁ (h₂.trans h₃)

#print axioms liftFrom_eq_self_of_code_le
#print axioms substAt_eq_self_of_code_le
#print axioms directAbsKey_lt
end LambdaTuring
