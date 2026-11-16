/-
Copyright (c) 2026 Erdős overlap formalization contributors.
Released under BSD-3-Clause license as described in the file LICENSE.
-/
module

public import ErdosOverlap.Native6WitnessModeFacts
public import ErdosOverlap.Certificate.FrontierWitness00
public import ErdosOverlap.Certificate.FrontierWitness01
public import ErdosOverlap.Certificate.FrontierWitness02
public import ErdosOverlap.Certificate.FrontierWitness03
public import ErdosOverlap.Certificate.FrontierWitness04
public import ErdosOverlap.Certificate.FrontierWitness05
public import ErdosOverlap.Certificate.FrontierWitness06
public import ErdosOverlap.Certificate.FrontierWitness07
public import ErdosOverlap.Certificate.FrontierWitness08
public import ErdosOverlap.Certificate.FrontierWitness09

namespace ErdosOverlap.FrontierWitnesses
open MeasureTheory Set
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

noncomputable def modeWitness (mode : Fin 20) : ℝ → ℝ :=
  match mode.val with
  | 0 => Native6Witnesses.v00
  | 1 => Native6Witnesses.v01
  | 2 => Native6Witnesses.v02
  | 3 => Native6Witnesses.v03
  | 4 => Native6Witnesses.v04
  | 5 => Native6Witnesses.v05
  | 6 => Native6Witnesses.v06
  | 7 => Native6Witnesses.v07
  | 8 => Native6Witnesses.v08
  | 9 => Native6Witnesses.v09
  | 10 => v00
  | 11 => v01
  | 12 => v02
  | 13 => v03
  | 14 => v04
  | 15 => v05
  | 16 => v06
  | 17 => v07
  | 18 => v08
  | _ => v09

def modeTau (mode : Fin 20) : ℚ :=
  match mode.val with
  | 0 => Native6Witnesses.tau00
  | 1 => Native6Witnesses.tau01
  | 2 => Native6Witnesses.tau02
  | 3 => Native6Witnesses.tau03
  | 4 => Native6Witnesses.tau04
  | 5 => Native6Witnesses.tau05
  | 6 => Native6Witnesses.tau06
  | 7 => Native6Witnesses.tau07
  | 8 => Native6Witnesses.tau08
  | 9 => Native6Witnesses.tau09
  | 10 => tau00
  | 11 => tau01
  | 12 => tau02
  | 13 => tau03
  | 14 => tau04
  | 15 => tau05
  | 16 => tau06
  | 17 => tau07
  | 18 => tau08
  | _ => tau09

def modeIv (mode : Fin 20) : ℚ :=
  match mode.val with
  | 0 => Native6Witnesses.Iv00
  | 1 => Native6Witnesses.Iv01
  | 2 => Native6Witnesses.Iv02
  | 3 => Native6Witnesses.Iv03
  | 4 => Native6Witnesses.Iv04
  | 5 => Native6Witnesses.Iv05
  | 6 => Native6Witnesses.Iv06
  | 7 => Native6Witnesses.Iv07
  | 8 => Native6Witnesses.Iv08
  | 9 => Native6Witnesses.Iv09
  | 10 => Iv00
  | 11 => Iv01
  | 12 => Iv02
  | 13 => Iv03
  | 14 => Iv04
  | 15 => Iv05
  | 16 => Iv06
  | 17 => Iv07
  | 18 => Iv08
  | _ => Iv09

def modeSlopeCache (mode : Fin 20) : PLSlopeCache :=
  match mode.val with
  | 0 => Native6Witnesses.slopeCache00
  | 1 => Native6Witnesses.slopeCache01
  | 2 => Native6Witnesses.slopeCache02
  | 3 => Native6Witnesses.slopeCache03
  | 4 => Native6Witnesses.slopeCache04
  | 5 => Native6Witnesses.slopeCache05
  | 6 => Native6Witnesses.slopeCache06
  | 7 => Native6Witnesses.slopeCache07
  | 8 => Native6Witnesses.slopeCache08
  | 9 => Native6Witnesses.slopeCache09
  | 10 => slopeCache00
  | 11 => slopeCache01
  | 12 => slopeCache02
  | 13 => slopeCache03
  | 14 => slopeCache04
  | 15 => slopeCache05
  | 16 => slopeCache06
  | 17 => slopeCache07
  | 18 => slopeCache08
  | _ => slopeCache09

def modeFirstCell (mode : Fin 20) : ℕ := (modeSlopeCache mode).firstCell

def modeTailCells (mode : Fin 20) : ℕ := (modeSlopeCache mode).numerators.size

def cachedLambda (mode : Fin 20) (j : ℕ) : ℚ :=
  (modeSlopeCache mode).value 1000000000000000000 j

theorem modeWitness_absolutelyContinuous (mode : Fin 20) :
    AbsolutelyContinuousOnInterval (modeWitness mode) 0 1 := by
  fin_cases mode
  · exact Native6Witnesses.v00_absolutelyContinuous
  · exact Native6Witnesses.v01_absolutelyContinuous
  · exact Native6Witnesses.v02_absolutelyContinuous
  · exact Native6Witnesses.v03_absolutelyContinuous
  · exact Native6Witnesses.v04_absolutelyContinuous
  · exact Native6Witnesses.v05_absolutelyContinuous
  · exact Native6Witnesses.v06_absolutelyContinuous
  · exact Native6Witnesses.v07_absolutelyContinuous
  · exact Native6Witnesses.v08_absolutelyContinuous
  · exact Native6Witnesses.v09_absolutelyContinuous
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

theorem modeWitness_one (mode : Fin 20) : modeWitness mode 1 = 0 := by
  fin_cases mode
  · exact Native6Witnesses.v00_one
  · exact Native6Witnesses.v01_one
  · exact Native6Witnesses.v02_one
  · exact Native6Witnesses.v03_one
  · exact Native6Witnesses.v04_one
  · exact Native6Witnesses.v05_one
  · exact Native6Witnesses.v06_one
  · exact Native6Witnesses.v07_one
  · exact Native6Witnesses.v08_one
  · exact Native6Witnesses.v09_one
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

theorem modeWitness_integral_abs_le (mode : Fin 20) :
    (∫ t in (0 : ℝ)..1, |modeWitness mode t|) ≤ (modeIv mode : ℝ) := by
  fin_cases mode
  · exact Native6Witnesses.v00_integral_abs.le
  · exact Native6Witnesses.v01_integral_abs.le
  · exact Native6Witnesses.v02_integral_abs.le
  · exact Native6Witnesses.v03_integral_abs.le
  · exact Native6Witnesses.v04_integral_abs.le
  · exact Native6Witnesses.v05_integral_abs.le
  · exact Native6Witnesses.v06_integral_abs.le
  · exact Native6Witnesses.v07_integral_abs.le
  · exact Native6Witnesses.v08_integral_abs.le
  · exact Native6Witnesses.v09_integral_abs.le
  · exact v00_integral_abs_le
  · exact v01_integral_abs_le
  · exact v02_integral_abs_le
  · exact v03_integral_abs_le
  · exact v04_integral_abs_le
  · exact v05_integral_abs_le
  · exact v06_integral_abs_le
  · exact v07_integral_abs_le
  · exact v08_integral_abs_le
  · exact v09_integral_abs_le

theorem mode_dualSlope_before (mode : Fin 20) {l r : ℝ}
    (hr : r ≤ (modeFirstCell mode : ℝ)/16384) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (modeTau mode : ℝ) (modeWitness mode) t = 2*(modeTau mode : ℝ) := by
  fin_cases mode
  · exact Native6Witnesses.dualSlope00_before hr
  · exact Native6Witnesses.dualSlope01_before hr
  · exact Native6Witnesses.dualSlope02_before hr
  · exact Native6Witnesses.dualSlope03_before hr
  · exact Native6Witnesses.dualSlope04_before hr
  · exact Native6Witnesses.dualSlope05_before hr
  · exact Native6Witnesses.dualSlope06_before hr
  · exact Native6Witnesses.dualSlope07_before hr
  · exact Native6Witnesses.dualSlope08_before hr
  · exact Native6Witnesses.dualSlope09_before hr
  · exact dualSlope00_before hr
  · exact dualSlope01_before hr
  · exact dualSlope02_before hr
  · exact dualSlope03_before hr
  · exact dualSlope04_before hr
  · exact dualSlope05_before hr
  · exact dualSlope06_before hr
  · exact dualSlope07_before hr
  · exact dualSlope08_before hr
  · exact dualSlope09_before hr

theorem mode_dualSlope_on_leaf (mode : Fin 20) {j : ℕ}
    (hj : j < modeTailCells mode) {l r : ℝ}
    (hl : (((modeFirstCell mode+j : ℕ) : ℝ)/16384) ≤ l)
    (hr : r ≤ ((((modeFirstCell mode+j : ℕ) : ℝ)+1)/16384)) :
    ∀ᵐ t ∂volume.restrict (Ioo l r),
      dualSlope (modeTau mode : ℝ) (modeWitness mode) t = (cachedLambda mode j : ℝ) := by
  fin_cases mode
  · exact Native6Witnesses.dualSlope00_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope01_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope02_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope03_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope04_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope05_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope06_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope07_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope08_on_leaf hj hl hr
  · exact Native6Witnesses.dualSlope09_on_leaf hj hl hr
  · exact dualSlope00_on_leaf hj hl hr
  · exact dualSlope01_on_leaf hj hl hr
  · exact dualSlope02_on_leaf hj hl hr
  · exact dualSlope03_on_leaf hj hl hr
  · exact dualSlope04_on_leaf hj hl hr
  · exact dualSlope05_on_leaf hj hl hr
  · exact dualSlope06_on_leaf hj hl hr
  · exact dualSlope07_on_leaf hj hl hr
  · exact dualSlope08_on_leaf hj hl hr
  · exact dualSlope09_on_leaf hj hl hr

/-- A small decidable leaf check: `none` selects the common zero prefix;
`some j` selects cached cell offset `j`. The supplied rational lambda is
checked against the physical witness slope, not merely stored as metadata. -/
def slopeLeafCheck (mode : Fin 20) (cell : Option ℕ) (l r lam : ℚ) : Bool :=
  match cell with
  | none => decide (r ≤ (modeFirstCell mode : ℚ)/16384 ∧ lam = 2*modeTau mode)
  | some j => decide (j < modeTailCells mode ∧
      ((modeFirstCell mode+j : ℕ) : ℚ)/16384 ≤ l ∧
      r ≤ ((((modeFirstCell mode+j : ℕ) : ℚ)+1)/16384) ∧ lam = cachedLambda mode j)

theorem slopeLeafCheck_sound (mode : Fin 20) (cell : Option ℕ) (l r lam : ℚ)
    (hc : slopeLeafCheck mode cell l r lam = true) :
    ∀ᵐ t ∂volume.restrict (Ioo (l : ℝ) (r : ℝ)),
      dualSlope (modeTau mode : ℝ) (modeWitness mode) t = (lam : ℝ) := by
  cases cell with
  | none =>
      have hs : r ≤ (modeFirstCell mode : ℚ)/16384 ∧ lam = 2*modeTau mode :=
        of_decide_eq_true hc
      have hp := mode_dualSlope_before mode (l := (l : ℝ)) (r := (r : ℝ))
        (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
          using (Rat.cast_le (K := ℝ)).2 hs.1)
      filter_upwards [hp] with t ht
      rw [ht, hs.2]
      push_cast
      rfl
  | some j =>
      have hs : j < modeTailCells mode ∧
          ((modeFirstCell mode+j : ℕ) : ℚ)/16384 ≤ l ∧
          r ≤ ((((modeFirstCell mode+j : ℕ) : ℚ)+1)/16384) ∧ lam = cachedLambda mode j :=
        of_decide_eq_true hc
      rw [hs.2.2.2]
      exact mode_dualSlope_on_leaf mode hs.1
        (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
          using (Rat.cast_le (K := ℝ)).2 hs.2.1)
        (by simpa only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
          using (Rat.cast_le (K := ℝ)).2 hs.2.2.1)

end
end ErdosOverlap.FrontierWitnesses
