/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.Integer
public import Mathlib.Algebra.BigOperators.Fin

/-!
# A linear-time exact dot-product checker

The logical definition of a finite matrix uses finite-index functions. For
certificate evaluation, paired list recursion avoids repeated indexed lookups.
The equivalence to the finite-sum definition is proved here. Short factor rows
are padded by zeros, allowing triangular factors to omit their zero tails.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

def listDot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + listDot xs ys

theorem listDot_eq_sum {n : ℕ} (xs ys : List ℤ)
    (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    listDot xs ys = ∑ k : Fin n, xs.getD k.val 0 * ys.getD k.val 0 := by
  induction n generalizing xs ys with
  | zero =>
    have hxs : xs = [] := List.eq_nil_iff_length_eq_zero.mpr (Nat.le_zero.mp hx)
    subst xs
    simp [listDot]
  | succ n ih =>
    cases xs with
    | nil => simp [listDot]
    | cons x xs =>
      cases ys with
      | nil => simp [listDot]
      | cons y ys =>
        have hx' : xs.length ≤ n := Nat.le_of_succ_le_succ hx
        have hy' : ys.length ≤ n := Nat.le_of_succ_le_succ hy
        rw [listDot, Fin.sum_univ_succ, ih xs ys hx' hy']
        simp only [Fin.val_zero, Fin.val_succ, List.getD_cons_zero,
          List.getD_cons_succ]

def factorMatrix {n : ℕ} (b : Array (List ℤ)) (i k : Fin n) : ℤ :=
  (b.getD i.val []).getD k.val 0

def fastResidual {n : ℕ} (a : Array (Array ℤ)) (b : Array (List ℤ))
    (s c : ℤ) (i j : Fin n) : ℤ :=
  c ^ 2 * tableMatrix a i j - s * listDot (b.getD i.val []) (b.getD j.val [])

theorem fastResidual_eq {n : ℕ}
    (a : Array (Array ℤ)) (b : Array (List ℤ)) (s c : ℤ)
    (hlen : ∀ i : Fin n, (b.getD i.val []).length ≤ n) :
    fastResidual (n := n) a b s c = intResidual (tableMatrix a) (factorMatrix b) s c := by
  funext i j
  simp only [fastResidual, intResidual, intGram, factorMatrix]
  rw [listDot_eq_sum _ _ (hlen i) (hlen j)]

/-- Kernel evaluation of the fast integer criterion implies the real PSD
statement for the exact rational matrix represented by the integer table. -/
theorem form_nonneg_of_fast_residual {n : ℕ}
    (a : Array (Array ℤ)) (b : Array (List ℤ)) (s c : ℤ)
    (hs : 0 < s) (hc : 0 < c)
    (hlen : ∀ i : Fin n, (b.getD i.val []).length ≤ n)
    (hsym : ∀ i j : Fin n, tableMatrix a i j = tableMatrix a j i)
    (hdd : IntDiagonallyDominant (fastResidual (n := n) a b s c))
    (x : Fin n → ℝ) :
    0 ≤ form (fun i j => (tableMatrix a i j : ℝ) / (s : ℝ)) x := by
  apply form_nonneg_of_int_residual_div (tableMatrix a) (factorMatrix b) s c hs hc hsym
  rwa [← fastResidual_eq a b s c hlen]

end ErdosOverlap.Gram
