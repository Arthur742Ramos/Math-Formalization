/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Certificate.Native6WitnessSlopes

/-!
# Actual witness regularity and exact costs through the cached mode interface

These are finite applications of the ten already proved witness theorems.
The exact absolute integrals are unchanged by the derivative cache.
-/

@[expose] public section

namespace ErdosOverlap.Native6Witnesses

open MeasureTheory

def modeIv (mode : Fin 10) : ℚ :=
  match mode.val with
  | 0 => Iv00
  | 1 => Iv01
  | 2 => Iv02
  | 3 => Iv03
  | 4 => Iv04
  | 5 => Iv05
  | 6 => Iv06
  | 7 => Iv07
  | 8 => Iv08
  | _ => Iv09

theorem modeWitness_absolutelyContinuous (mode : Fin 10) :
    AbsolutelyContinuousOnInterval (modeWitness mode) 0 1 := by
  fin_cases mode
  · exact v00_absolutelyContinuous
  · exact v01_absolutelyContinuous
  · exact v02_absolutelyContinuous
  · exact v03_absolutelyContinuous
  · exact v04_absolutelyContinuous
  · exact v05_absolutelyContinuous
  · exact v06_absolutelyContinuous
  · exact v07_absolutelyContinuous
  · exact v08_absolutelyContinuous
  · exact v09_absolutelyContinuous

theorem modeWitness_one (mode : Fin 10) : modeWitness mode 1 = 0 := by
  fin_cases mode
  · exact v00_one
  · exact v01_one
  · exact v02_one
  · exact v03_one
  · exact v04_one
  · exact v05_one
  · exact v06_one
  · exact v07_one
  · exact v08_one
  · exact v09_one

theorem modeWitness_zero (mode : Fin 10) : modeWitness mode 0 = 0 := by
  fin_cases mode
  · exact v00_zero
  · exact v01_zero
  · exact v02_zero
  · exact v03_zero
  · exact v04_zero
  · exact v05_zero
  · exact v06_zero
  · exact v07_zero
  · exact v08_zero
  · exact v09_zero

theorem modeWitness_nonneg (mode : Fin 10) (t : ℝ) : 0 ≤ modeWitness mode t := by
  fin_cases mode
  · exact v00_nonneg t
  · exact v01_nonneg t
  · exact v02_nonneg t
  · exact v03_nonneg t
  · exact v04_nonneg t
  · exact v05_nonneg t
  · exact v06_nonneg t
  · exact v07_nonneg t
  · exact v08_nonneg t
  · exact v09_nonneg t

theorem modeWitness_integral_abs (mode : Fin 10) :
    (∫ t in (0 : ℝ)..1, |modeWitness mode t|) = (modeIv mode : ℝ) := by
  fin_cases mode
  · exact v00_integral_abs
  · exact v01_integral_abs
  · exact v02_integral_abs
  · exact v03_integral_abs
  · exact v04_integral_abs
  · exact v05_integral_abs
  · exact v06_integral_abs
  · exact v07_integral_abs
  · exact v08_integral_abs
  · exact v09_integral_abs

end ErdosOverlap.Native6Witnesses
