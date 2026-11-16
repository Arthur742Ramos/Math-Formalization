/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.PhaseAlgebra
public import ErdosOverlap.Gram.HatBaseline
public import ErdosOverlap.Gram.HatBounds

/-!
# From exact raw phase data to the physical signed functional

The finite certificate fields are integer data, multiplier signs, exact
triangle assembly, and a PSD statement. The analytic conclusions below are
derived for arbitrary admissible measurable partitions.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open MeasureTheory Set
open scoped Interval BigOperators

noncomputable def gridBase (N : ℕ) (a : ℝ) (k : Fin (N+1)) : ℝ :=
  if k.val = 0 then 1/2-a/12 else if k.val=N then a/24 else (2-(k.val : ℝ)*a)/4

noncomputable def diagonalBound (N : ℕ) (i : Fin (N+1)) : ℝ :=
  if i.val=0 ∨ i.val=N then 1/3 else 1

theorem phaseIntegerFull_normalized {N : ℕ} (hN : 0 < N) (d : ℤ) (hd : d ≠ 0)
    (diagonal gamma nonnegative : Array ℤ) (eta : ℤ)
    (ts : List (Triangle (N+1))) (T : IntMatrix (N+1))
    (hT : triangleAggregate ts = T) :
    scaledIntegerMatrix (phaseIntegerFull (N := N) diagonal gamma nonnegative eta T)
        (8 * (N : ℤ)^2 * d) =
      phaseMatrix (2/(N : ℝ))
        (fun i => (diagonal.getD i.val 0 : ℝ)/(d : ℝ))
        (fun k => (gamma.getD k.val 0 : ℝ)/(d : ℝ))
        (fun k => (nonnegative.getD k.val 0 : ℝ)/(d : ℝ))
        ((eta : ℝ)/(d : ℝ)) (d : ℝ) ts := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  funext i j
  rw [← hT]
  simp only [scaledIntegerMatrix, phaseIntegerFull, phaseMatrix, distanceIndex,
    triangleSumMatrix, triangleAggregate_apply, Int.cast_add, Int.cast_sub, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    field_simp
    ring
  · simp only [hij, ↓reduceIte, Int.cast_zero, Int.cast_mul,
      Int.cast_natCast, Int.cast_ofNat]
    field_simp
    ring

structure RawPhaseCertificate (N : ℕ) where
  denominator : ℤ
  diagonal : Array ℤ
  gamma : Array ℤ
  nonnegative : Array ℤ
  eta : ℤ
  triangles : List (Triangle (N+1))
  triangleTable : IntMatrix (N+1)
  cells_pos : 0 < N
  denominator_pos : 0 < denominator
  diagonal_nonnegative : ∀ i : Fin (N+1), 0 ≤ diagonal.getD i.val 0
  auxiliary_nonnegative : ∀ i : Fin (N+1), 0 ≤ nonnegative.getD i.val 0
  eta_nonnegative : 0 ≤ eta
  triangles_valid : ∀ t ∈ triangles, t.Valid
  triangle_aggregation : triangleAggregate triangles = triangleTable
  full_nonnegative : ∀ y : Fin (N+1) → ℝ, (∑ i, y i) = 0 →
    0 ≤ form (scaledIntegerMatrix
      (phaseIntegerFull (N := N) diagonal gamma nonnegative eta triangleTable)
      (8 * (N : ℤ)^2 * denominator)) y

def RawPhaseCertificate.gammaRational {N : ℕ} (c : RawPhaseCertificate N) : Array ℚ :=
  c.gamma.map (fun z : ℤ => (z : ℚ)/(c.denominator : ℚ))

def RawPhaseCertificate.lowerRational {N : ℕ} (c : RawPhaseCertificate N) : ℚ :=
  phaseLowerRational N c.denominator c.diagonal c.gamma c.nonnegative c.eta c.triangles

def RawPhaseCertificate.meanCoefficient {N : ℕ} (c : RawPhaseCertificate N) : ℚ :=
  -(c.eta : ℚ)*(N : ℚ)^2/(4*(c.denominator : ℚ))

theorem RawPhaseCertificate.width_pos {N : ℕ} (c : RawPhaseCertificate N) :
    0 < (2 : ℝ)/N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast c.cells_pos
  exact div_pos (by norm_num) hn

theorem RawPhaseCertificate.width_mul {N : ℕ} (c : RawPhaseCertificate N) :
    (N : ℝ)*((2 : ℝ)/N)=2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt c.cells_pos
  field_simp

theorem RawPhaseCertificate.matrix_nonnegative {N : ℕ} (c : RawPhaseCertificate N)
    (y : Fin (N+1) → ℝ) (hy : ∑ i, y i = 0) :
    0 ≤ form (phaseMatrix (2/(N : ℝ))
      (fun i => (c.diagonal.getD i.val 0 : ℝ)/(c.denominator : ℝ))
      (fun k => (c.gamma.getD k.val 0 : ℝ)/(c.denominator : ℝ))
      (fun k => (c.nonnegative.getD k.val 0 : ℝ)/(c.denominator : ℝ))
      ((c.eta : ℝ)/(c.denominator : ℝ)) (c.denominator : ℝ) c.triangles) y := by
  rw [← phaseIntegerFull_normalized c.cells_pos c.denominator c.denominator_pos.ne'
    c.diagonal c.gamma c.nonnegative c.eta c.triangles c.triangleTable c.triangle_aggregation]
  exact c.full_nonnegative y hy

def baseInteger (N : ℕ) (k : Fin (N+1)) : ℤ :=
  if k.val=0 then 6*(N : ℤ)-2 else if k.val=N then 1 else 6*((N : ℤ)-(k.val : ℤ))

def diagonalInteger (N : ℕ) (i : Fin (N+1)) : ℤ :=
  if i.val=0 ∨ i.val=N then 4*(N : ℤ) else 12*(N : ℤ)

theorem baseInteger_ratio {N : ℕ} (hN : 0 < N) (k : Fin (N+1)) :
    (baseInteger N k : ℝ)/(12*(N : ℝ)) = gridBase N (2/(N : ℝ)) k := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hN
  unfold baseInteger gridBase
  split_ifs <;> push_cast <;> field_simp <;> ring

theorem diagonalInteger_ratio {N : ℕ} (hN : 0 < N) (i : Fin (N+1)) :
    (diagonalInteger N i : ℝ)/(12*(N : ℝ)) = diagonalBound N i := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hN
  unfold diagonalInteger diagonalBound
  split_ifs <;> push_cast <;> field_simp
  norm_num

theorem phaseLowerRational_cast {N : ℕ} (hN : 0 < N) (d : ℤ) (hd : d ≠ 0)
    (diagonal gamma nonnegative : Array ℤ) (eta : ℤ) (ts : List (Triangle (N+1))) :
    (phaseLowerRational N d diagonal gamma nonnegative eta ts : ℝ) =
      (∑ k : Fin (N+1), ((gamma.getD k.val 0 : ℝ)/(d : ℝ) -
        (nonnegative.getD k.val 0 : ℝ)/(d : ℝ))*gridBase N (2/(N : ℝ)) k) -
      (∑ i : Fin (N+1), ((diagonal.getD i.val 0 : ℝ)/(d : ℝ))*diagonalBound N i) -
      ((eta : ℝ)/(d : ℝ))/12 - (ts.map (fun t => (t.weight : ℝ)/(d : ℝ))).sum := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hN
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hb : (∑ k : Fin (N+1), ((gamma.getD k.val 0 : ℝ)/(d : ℝ) -
      (nonnegative.getD k.val 0 : ℝ)/(d : ℝ))*gridBase N (2/(N : ℝ)) k) =
      ((∑ k : Fin (N+1), baseInteger N k *
        (gamma.getD k.val 0 - nonnegative.getD k.val 0) : ℤ) : ℝ) /
        (12*(N : ℝ)*(d : ℝ)) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_sub, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← baseInteger_ratio hN k]
    field_simp
  have hdiag : (∑ i : Fin (N+1), ((diagonal.getD i.val 0 : ℝ)/(d : ℝ))*diagonalBound N i) =
      ((∑ i : Fin (N+1), diagonalInteger N i * diagonal.getD i.val 0 : ℤ) : ℝ) /
        (12*(N : ℝ)*(d : ℝ)) := by
    simp only [Int.cast_sum, Int.cast_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← diagonalInteger_ratio hN i]
    field_simp
  have hw : (ts.map (fun t => (t.weight : ℝ)/(d : ℝ))).sum =
      ((ts.map Triangle.weight).sum : ℤ)/(d : ℝ) := by
    induction ts with
    | nil => simp
    | cons t ts ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, add_div, ih]
  have hl : (phaseLowerRational N d diagonal gamma nonnegative eta ts : ℝ) =
      (((∑ k : Fin (N+1), baseInteger N k *
        (gamma.getD k.val 0 - nonnegative.getD k.val 0) : ℤ) : ℝ) -
        ((∑ i : Fin (N+1), diagonalInteger N i * diagonal.getD i.val 0 : ℤ) : ℝ) -
        (N : ℝ)*(eta : ℝ) - 12*(N : ℝ)*((ts.map Triangle.weight).sum : ℤ)) /
        (12*(N : ℝ)*(d : ℝ)) := by
    simp only [phaseLowerRational, phaseLowerNumerator, baseInteger, diagonalInteger,
      Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, Rat.cast_ofNat,
      Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  rw [hl, hb, hdiag, hw]
  field_simp

end ErdosOverlap.Gram
