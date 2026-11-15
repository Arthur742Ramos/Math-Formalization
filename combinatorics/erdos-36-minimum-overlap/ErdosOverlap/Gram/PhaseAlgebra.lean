/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.Lag

/-!
# Algebraic extraction of a signed phase functional

The theorem in this file combines an actual PSD trace with diagonal, lag,
triangle and mean constraints. Functional weights may have either sign;
only the auxiliary inequality multipliers are required to be nonnegative.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

theorem tracePair_add {ι : Type*} [Fintype ι] (A B X : ι → ι → ℝ) :
    tracePair (fun i j => A i j + B i j) X = tracePair A X + tracePair B X := by
  simp only [tracePair, add_mul, Finset.sum_add_distrib]

theorem tracePair_sub {ι : Type*} [Fintype ι] (A B X : ι → ι → ℝ) :
    tracePair (fun i j => A i j - B i j) X = tracePair A X - tracePair B X := by
  simp only [tracePair, sub_mul, Finset.sum_sub_distrib]

theorem tracePair_scale {ι : Type*} [Fintype ι] (a : ℝ) (A X : ι → ι → ℝ) :
    tracePair (fun i j => a * A i j) X = a * tracePair A X := by
  simp only [tracePair, mul_assoc, Finset.mul_sum]

theorem tracePair_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (X : ι → ι → ℝ) :
    tracePair (fun i j => if i = j then d i else 0) X = ∑ i, d i * X i i := by
  simp [tracePair, ite_mul]

theorem tracePair_pairIndicator {n : ℕ} (i j : Fin n) (X : Fin n → Fin n → ℝ) :
    tracePair (fun p q => (pairIndicator i j p q : ℝ)) X = X i j + X j i := by
  simp [tracePair, pairIndicator, Int.cast_add, add_mul, ite_and, ite_mul,
    Finset.sum_add_distrib]

noncomputable def triangleValue {n : ℕ} (t : Triangle n) (X : Fin n → Fin n → ℝ) : ℝ :=
  (t.s0 : ℝ) * X t.i t.j + (t.s1 : ℝ) * X t.j t.k + (t.s2 : ℝ) * X t.i t.k

theorem tracePair_triangle {n : ℕ} (t : Triangle n) (X : Fin n → Fin n → ℝ)
    (hX : ∀ i j, X i j = X j i) :
    tracePair (fun i j => (t.coefficient i j : ℝ)) X =
      2 * (t.weight : ℝ) * triangleValue t X := by
  simp only [Triangle.coefficient, Int.cast_mul, Int.cast_add]
  rw [tracePair_scale, tracePair_add, tracePair_add, tracePair_scale, tracePair_scale,
    tracePair_scale, tracePair_pairIndicator, tracePair_pairIndicator, tracePair_pairIndicator]
  rw [hX t.j t.i, hX t.k t.j, hX t.k t.i]
  unfold triangleValue
  ring

noncomputable def triangleSumMatrix {n : ℕ} (ts : List (Triangle n)) (d : ℝ)
    (i j : Fin n) : ℝ := ((ts.map (fun t => t.coefficient i j)).sum : ℤ) / (2*d)

theorem tracePair_triangleSum {n : ℕ} (ts : List (Triangle n)) (d : ℝ) (hd : d ≠ 0)
    (X : Fin n → Fin n → ℝ) (hX : ∀ i j, X i j = X j i) :
    tracePair (triangleSumMatrix ts d) X =
      (ts.map (fun t => (t.weight : ℝ)/d * triangleValue t X)).sum := by
  induction ts with
  | nil => simp [triangleSumMatrix, tracePair]
  | cons t ts ih =>
    have heq : triangleSumMatrix (t :: ts) d =
        fun i j => (1/(2*d)) * (t.coefficient i j : ℝ) + triangleSumMatrix ts d i j := by
      funext i j
      simp only [triangleSumMatrix, List.map_cons, List.sum_cons, Int.cast_add, add_div]
      ring
    rw [heq, tracePair_add, tracePair_scale, tracePair_triangle t X hX, ih]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    field_simp

noncomputable def phaseMatrix {N : ℕ} (a : ℝ)
    (diagonal gamma nonnegative : Fin (N+1) → ℝ) (eta d : ℝ)
    (ts : List (Triangle (N+1))) (i j : Fin (N+1)) : ℝ :=
  (if i = j then diagonal i else 0) -
    (a/4) * ((gamma (distanceIndex i j) - nonnegative (distanceIndex i j)) *
      (if i = j then 1 else 1/2)) +
    eta * ((i.val : ℝ)*a*((j.val : ℝ)*a)) + triangleSumMatrix ts d i j

theorem phaseMatrix_trace {N : ℕ} (a : ℝ)
    (diagonal gamma nonnegative : Fin (N+1) → ℝ) (eta d : ℝ) (hd : d ≠ 0)
    (ts : List (Triangle (N+1))) (X : Fin (N+1) → Fin (N+1) → ℝ)
    (hX : ∀ i j, X i j = X j i) :
    tracePair (phaseMatrix a diagonal gamma nonnegative eta d ts) X =
      (∑ i, diagonal i * X i i) -
        (a/4) * (∑ k, (gamma k - nonnegative k) * lagTrace X k) +
        eta * tracePair (fun i j => (i.val : ℝ)*a*((j.val : ℝ)*a)) X +
        (ts.map (fun t => (t.weight : ℝ)/d * triangleValue t X)).sum := by
  unfold phaseMatrix
  rw [tracePair_add, tracePair_add, tracePair_sub, tracePair_diagonal,
    tracePair_scale, tracePair_scale, tracePair_triangleSum ts d hd X hX,
    ← weighted_lagTrace X (fun k => gamma k - nonnegative k)]

theorem triangle_weighted_bound {n : ℕ} (ts : List (Triangle n)) {d : ℝ}
    (hd : 0 < d) (X : Fin n → Fin n → ℝ)
    (hw : ∀ t ∈ ts, 0 ≤ t.weight) (ht : ∀ t ∈ ts, triangleValue t X ≤ 1) :
    (ts.map (fun t => (t.weight : ℝ)/d * triangleValue t X)).sum ≤
      (ts.map (fun t => (t.weight : ℝ)/d)).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    have hwt : (0 : ℝ) ≤ (t.weight : ℝ) := by exact_mod_cast hw t (by simp)
    have ht' := ht t (by simp)
    have hhead : (t.weight : ℝ)/d * triangleValue t X ≤ (t.weight : ℝ)/d := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left ht' (div_nonneg hwt hd.le)
    apply add_le_add hhead
    exact ih (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      (fun u hu => ht u (List.mem_cons_of_mem _ hu))

/-- A signed functional follows from the exact finite matrix and the stated
physical covariance inequalities. No target lower-bound conclusion is a
hypothesis of this theorem. -/
theorem phaseFunctional_of_covariance {N : ℕ} (a d eta B : ℝ)
    (diagonal gamma nonnegative base diagonalBound y : Fin (N+1) → ℝ)
    (ts : List (Triangle (N+1))) (X : Fin (N+1) → Fin (N+1) → ℝ)
    (hd : 0 < d) (heta : 0 ≤ eta)
    (hdiag : ∀ i, 0 ≤ diagonal i) (hnu : ∀ i, 0 ≤ nonnegative i)
    (hw : ∀ t ∈ ts, 0 ≤ t.weight)
    (hX : ∀ i j, X i j = X j i)
    (htrace : 0 ≤ tracePair (phaseMatrix a diagonal gamma nonnegative eta d ts) X)
    (hdiagonal : ∀ i, X i i ≤ diagonalBound i)
    (hmean : tracePair (fun i j => (i.val : ℝ)*a*((j.val : ℝ)*a)) X ≤ B)
    (htriangle : ∀ t ∈ ts, triangleValue t X ≤ 1)
    (hy : ∀ k, y k = base k - (a/4) * lagTrace X k)
    (hy0 : ∀ k, 0 ≤ y k) :
    (∑ k, (gamma k - nonnegative k) * base k) -
      (∑ i, diagonal i * diagonalBound i) - eta * B -
      (ts.map (fun t => (t.weight : ℝ)/d)).sum ≤ ∑ k, gamma k * y k := by
  have hdb : (∑ i, diagonal i * X i i) ≤ ∑ i, diagonal i * diagonalBound i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hdiagonal i) (hdiag i)
  have hmb := mul_le_mul_of_nonneg_left hmean heta
  have htb := triangle_weighted_bound ts hd X hw htriangle
  rw [phaseMatrix_trace a diagonal gamma nonnegative eta d hd.ne' ts X hX] at htrace
  have htotal : 0 ≤ (∑ i, diagonal i * diagonalBound i) -
      (a/4) * (∑ k, (gamma k - nonnegative k) * lagTrace X k) + eta * B +
      (ts.map (fun t => (t.weight : ℝ)/d)).sum := by linarith
  have hysum : (∑ k, (gamma k - nonnegative k) * y k) =
      (∑ k, (gamma k - nonnegative k) * base k) -
        (a/4) * (∑ k, (gamma k - nonnegative k) * lagTrace X k) := by
    simp_rw [hy]
    simp [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, mul_left_comm]
  have hfirst : (∑ k, (gamma k - nonnegative k) * base k) -
      (∑ i, diagonal i * diagonalBound i) - eta * B -
      (ts.map (fun t => (t.weight : ℝ)/d)).sum ≤
      ∑ k, (gamma k - nonnegative k) * y k := by rw [hysum]; linarith
  apply hfirst.trans
  apply Finset.sum_le_sum
  intro k hk
  have hn := mul_nonneg (hnu k) (hy0 k)
  nlinarith

end ErdosOverlap.Gram
