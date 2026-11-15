/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Gram.TriangleAssembly
public import ErdosOverlap.Gram.Restriction

/-!
# Exact common-denominator phase Gram data

All diagonal, functional, nonnegative, mean and triangle coefficients share
the positive integer denominator `d`.  With cell width `a = 2 / N`, scaling
the full phase Gram matrix by `8 * N^2 * d` gives the integer formula below.
The last coordinate is eliminated by a double difference.
-/

@[expose] public section

namespace ErdosOverlap.Gram

open scoped BigOperators

def natDistance (i j : ℕ) : ℕ := if i ≤ j then j - i else i - j

def phaseIntegerFull {N : ℕ} (diagonal gamma nonnegative : Array ℤ) (eta : ℤ)
    (triangles : IntMatrix (N + 1)) (i j : Fin (N + 1)) : ℤ :=
  (if i = j then 8 * (N : ℤ) ^ 2 * diagonal.getD i.val 0 else 0) -
    (if i = j then 4 * (N : ℤ) else 2 * (N : ℤ)) *
      (gamma.getD (natDistance i.val j.val) 0 -
        nonnegative.getD (natDistance i.val j.val) 0) +
    4 * (N : ℤ) ^ 2 * matrixEntry triangles i j +
    32 * eta * (i.val : ℤ) * (j.val : ℤ)

def restrictedInteger {N : ℕ} (G : Fin (N + 1) → Fin (N + 1) → ℤ)
    (i j : Fin N) : ℤ :=
  G i.castSucc j.castSucc - G i.castSucc (Fin.last N) -
    G (Fin.last N) j.castSucc + G (Fin.last N) (Fin.last N)

noncomputable def scaledIntegerMatrix {n : ℕ}
    (G : Fin n → Fin n → ℤ) (s : ℤ) (i j : Fin n) : ℝ :=
  (G i j : ℝ) / (s : ℝ)

theorem restricted_scaledIntegerMatrix {N : ℕ}
    (G : Fin (N + 1) → Fin (N + 1) → ℤ) (s : ℤ) :
    restricted (scaledIntegerMatrix G s) = scaledIntegerMatrix (restrictedInteger G) s := by
  funext i j
  simp only [restricted, scaledIntegerMatrix, restrictedInteger, Int.cast_add, Int.cast_sub,
    sub_div, add_div]

/-- A concrete restricted-table equality transfers its already proved PSD
property to every zero-sum vector of the actual full matrix. -/
theorem phase_nonnegative_on_sum_zero {N : ℕ}
    (G : Fin (N + 1) → Fin (N + 1) → ℤ)
    (A : Fin N → Fin N → ℤ) (s : ℤ)
    (hbind : ∀ i j, A i j = restrictedInteger G i j)
    (hA : ∀ x : Fin N → ℝ, 0 ≤ form (scaledIntegerMatrix A s) x)
    (y : Fin (N + 1) → ℝ) (hy : ∑ i, y i = 0) :
    0 ≤ form (scaledIntegerMatrix G s) y := by
  apply form_nonneg_on_sum_zero _ _ y hy
  intro x
  rw [restricted_scaledIntegerMatrix]
  have hfun : restrictedInteger G = A := by
    funext i j
    exact (hbind i j).symm
  rw [hfun]
  exact hA x

/-- The integer numerator of the mean-zero functional return, with denominator
`12 * N * d`. Endpoint cells use the exact square bound `1/3`. -/
def phaseLowerNumerator (N : ℕ) (diagonal gamma nonnegative : Array ℤ) (eta : ℤ)
    (triangles : List (Triangle (N + 1))) : ℤ :=
  (∑ k : Fin (N + 1),
    (if k.val = 0 then 6 * (N : ℤ) - 2
      else if k.val = N then 1 else 6 * ((N : ℤ) - (k.val : ℤ))) *
      (gamma.getD k.val 0 - nonnegative.getD k.val 0)) -
  (∑ i : Fin (N + 1),
    (if i.val = 0 ∨ i.val = N then 4 * (N : ℤ) else 12 * (N : ℤ)) *
      diagonal.getD i.val 0) -
  (N : ℤ) * eta - 12 * (N : ℤ) * (triangles.map Triangle.weight).sum

def phaseLowerRational (N : ℕ) (d : ℤ) (diagonal gamma nonnegative : Array ℤ) (eta : ℤ)
    (triangles : List (Triangle (N + 1))) : ℚ :=
  (phaseLowerNumerator N diagonal gamma nonnegative eta triangles : ℚ) /
    (12 * (N : ℚ) * (d : ℚ))

end ErdosOverlap.Gram
