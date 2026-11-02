/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
/-
These theorem holes are comparison obligations only. The solution does not
import this module. Computability and one-one reducibility use pinned Mathlib.
-/
module
public import Mathlib.Computability.Reduce

@[expose] public section
namespace LambdaTuring

theorem effective_isomorphism_of_oneOne (A B : Nat → Prop) (f g : Nat → Nat)
    (hfc : Computable f) (hgc : Computable g)
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (hfr : ∀ x, A x ↔ B (f x)) (hgr : ∀ y, B y ↔ A (g y)) :
    ∃ u v : Nat → Nat, Computable u ∧ Computable v ∧
      (∀ x, v (u x) = x) ∧ (∀ y, u (v y) = y) ∧ (∀ x, A x ↔ B (u x)) := by
  sorry

theorem computable_permutation_of_oneOneEquiv (A B : Nat → Prop)
    (h : OneOneEquiv A B) :
    ∃ e : Nat ≃ Nat, Computable e ∧ Computable e.symm ∧
      ∀ x, A x ↔ B (e x) := by
  sorry

end LambdaTuring
