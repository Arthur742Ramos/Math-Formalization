/-
Copyright (c) 2026. Released under the BSD-3-Clause license.
-/
module

public import ErdosOverlap.PeriodicGrid
public import ErdosOverlap.PhaseKernel

/-! # Exact data structures for the native kernel assembly -/

namespace ErdosOverlap

public section

structure PeriodicCellRow where
  firstPosition : ℕ
  lastPosition : ℕ
  cell : ℕ
  perimeter : Bool
  weight : ℚ
  deriving DecidableEq, Repr

@[expose] def PeriodicCellRow.valid (n : ℕ) (row : PeriodicCellRow) : Bool :=
  decide (0 < row.firstPosition ∧ row.firstPosition < row.lastPosition ∧
    row.cell < n ∧ row.weight ≤ 0)

@[expose] noncomputable def PeriodicCellRow.value (n : ℕ) (row : PeriodicCellRow) (t : ℝ) : ℝ :=
  (row.weight : ℝ) *
    if row.perimeter then
      periodicDilationKernel n row.firstPosition row.cell t +
        periodicDilationKernel n (row.lastPosition - row.firstPosition) row.cell t +
        periodicDilationKernel n row.lastPosition row.cell t
    else
      periodicDilationKernel n row.lastPosition row.cell t -
        periodicDilationKernel n row.firstPosition row.cell t -
        periodicDilationKernel n (row.lastPosition - row.firstPosition) row.cell t

@[expose] def PeriodicCellRow.lowerValue (row : PeriodicCellRow) : ℚ :=
  if row.perimeter then 2 * row.weight else 0

@[expose] noncomputable def periodicRowsKernel (n : ℕ) : List PeriodicCellRow → ℝ → ℝ
  | [], _ => 0
  | row :: rest, t => row.value n t + periodicRowsKernel n rest t

@[expose] def periodicRowsLower : List PeriodicCellRow → ℚ
  | [] => 0
  | row :: rest => row.lowerValue + periodicRowsLower rest

structure PhaseFunctionalRow where
  cells : ℕ
  multiplier : ℚ
  gamma : Array ℚ
  lowerAtZero : ℚ
  meanCoefficient : ℚ
  deriving DecidableEq, Repr

@[expose] def PhaseFunctionalRow.valid (row : PhaseFunctionalRow) : Bool :=
  decide (0 < row.cells ∧ row.gamma.size = row.cells + 1 ∧ 0 ≤ row.multiplier)

@[expose] noncomputable def PhaseFunctionalRow.value (row : PhaseFunctionalRow) (t : ℝ) : ℝ :=
  (row.multiplier : ℝ) * phaseKernel row.cells row.gamma t

@[expose] noncomputable def phaseRowsKernel : List PhaseFunctionalRow → ℝ → ℝ
  | [], _ => 0
  | row :: rest, t => row.value t + phaseRowsKernel rest t

@[expose] def phaseRowsLower : List PhaseFunctionalRow → ℚ
  | [] => 0
  | row :: rest => row.multiplier * row.lowerAtZero + phaseRowsLower rest

@[expose] def phaseRowsMeanCoefficient : List PhaseFunctionalRow → ℚ
  | [] => 0
  | row :: rest => row.multiplier * row.meanCoefficient + phaseRowsMeanCoefficient rest

end
end ErdosOverlap
