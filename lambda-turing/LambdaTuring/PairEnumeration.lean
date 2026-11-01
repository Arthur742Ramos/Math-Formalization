/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, and
Ruy José Guerra Barretto de Queiroz. All rights reserved.
Released under the Apache 2.0 license as described in the repository LICENSE.
-/
module

public import LambdaTuring.ChurchPredecessor
public meta import LambdaTuring.ChurchPredecessor

@[expose] public section

namespace LambdaTuring

/-- One step in the square-based enumeration used by Mathlib's `Nat.pair`. -/
def nextNumericPair (a b : Nat) : Nat × Nat :=
  if a < b then
    if a + 1 < b then (a + 1, b) else (b, 0)
  else if b < a then (a, b + 1) else (0, a + 1)

theorem nextNumericPair_code (a b : Nat) :
    Nat.pair (nextNumericPair a b).1 (nextNumericPair a b).2 = Nat.pair a b + 1 := by
  by_cases h : a < b
  · by_cases hs : a + 1 < b
    · simp [nextNumericPair, Nat.pair, h, hs, Nat.add_assoc]
    · have heq : a + 1 = b := by omega
      subst b
      simp [nextNumericPair, Nat.pair, Nat.add_mul, Nat.mul_add]; omega
  · by_cases hs : b < a
    · have hnext : ¬ a < b + 1 := by omega
      simp [nextNumericPair, Nat.pair, h, hs, hnext, Nat.add_assoc]
    · have heq : b = a := by omega
      subst b
      simp [nextNumericPair, Nat.pair, Nat.add_mul, Nat.mul_add]; omega

theorem unpair_pair_succ (a b : Nat) :
    Nat.unpair (Nat.pair a b + 1) = nextNumericPair a b := by
  have h := congrArg Nat.unpair (nextNumericPair_code a b)
  simpa using h.symm

theorem unpair_succ (n : Nat) :
    Nat.unpair (n + 1) = nextNumericPair n.unpair.1 n.unpair.2 := by
  simpa using unpair_pair_succ n.unpair.1 n.unpair.2

#print axioms nextNumericPair_code
#print axioms unpair_succ

end LambdaTuring
