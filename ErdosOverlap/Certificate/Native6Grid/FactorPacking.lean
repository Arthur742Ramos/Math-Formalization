module

public import ErdosOverlap.Certificate.Native6Grid.FactorRows
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def evenFactorRows : List (List ℤ) := (List.range 10).map (fun k => factorRow (2*k))
def oddFactorRows : List (List ℤ) := (List.range 10).map (fun k => factorRow (2*k+1))

theorem evenFactors_packed : factorPackingCheck 641 evenFactorRows packedFactorsEven = true := by
  decide +kernel

theorem oddFactors_packed : factorPackingCheck 641 oddFactorRows packedFactorsOdd = true := by
  decide +kernel

theorem factorMass00_checked : factorAbsSum00 = taylorFactorMass factors00 := by decide +kernel
theorem factorMass01_checked : factorAbsSum01 = taylorFactorMass factors01 := by decide +kernel
theorem factorMass02_checked : factorAbsSum02 = taylorFactorMass factors02 := by decide +kernel
theorem factorMass03_checked : factorAbsSum03 = taylorFactorMass factors03 := by decide +kernel
theorem factorMass04_checked : factorAbsSum04 = taylorFactorMass factors04 := by decide +kernel
theorem factorMass05_checked : factorAbsSum05 = taylorFactorMass factors05 := by decide +kernel
theorem factorMass06_checked : factorAbsSum06 = taylorFactorMass factors06 := by decide +kernel
theorem factorMass07_checked : factorAbsSum07 = taylorFactorMass factors07 := by decide +kernel
theorem factorMass08_checked : factorAbsSum08 = taylorFactorMass factors08 := by decide +kernel
theorem factorMass09_checked : factorAbsSum09 = taylorFactorMass factors09 := by decide +kernel
theorem factorMass10_checked : factorAbsSum10 = taylorFactorMass factors10 := by decide +kernel
theorem factorMass11_checked : factorAbsSum11 = taylorFactorMass factors11 := by decide +kernel
theorem factorMass12_checked : factorAbsSum12 = taylorFactorMass factors12 := by decide +kernel
theorem factorMass13_checked : factorAbsSum13 = taylorFactorMass factors13 := by decide +kernel
theorem factorMass14_checked : factorAbsSum14 = taylorFactorMass factors14 := by decide +kernel
theorem factorMass15_checked : factorAbsSum15 = taylorFactorMass factors15 := by decide +kernel
theorem factorMass16_checked : factorAbsSum16 = taylorFactorMass factors16 := by decide +kernel
theorem factorMass17_checked : factorAbsSum17 = taylorFactorMass factors17 := by decide +kernel
theorem factorMass18_checked : factorAbsSum18 = taylorFactorMass factors18 := by decide +kernel
theorem factorMass19_checked : factorAbsSum19 = taylorFactorMass factors19 := by decide +kernel

def factorMass (k : ℕ) : ℤ :=
  if k < 10 then
    if k < 5 then
      if k < 2 then
        if k < 1 then
          factorAbsSum00
        else
          factorAbsSum01
      else
        if k < 3 then
          factorAbsSum02
        else
          if k < 4 then
            factorAbsSum03
          else
            factorAbsSum04
    else
      if k < 7 then
        if k < 6 then
          factorAbsSum05
        else
          factorAbsSum06
      else
        if k < 8 then
          factorAbsSum07
        else
          if k < 9 then
            factorAbsSum08
          else
            factorAbsSum09
  else
    if k < 15 then
      if k < 12 then
        if k < 11 then
          factorAbsSum10
        else
          factorAbsSum11
      else
        if k < 13 then
          factorAbsSum12
        else
          if k < 14 then
            factorAbsSum13
          else
            factorAbsSum14
    else
      if k < 17 then
        if k < 16 then
          factorAbsSum15
        else
          factorAbsSum16
      else
        if k < 18 then
          factorAbsSum17
        else
          if k < 19 then
            factorAbsSum18
          else
            factorAbsSum19

theorem factorMass_correct (k : ℕ) (hk : k < 20) : factorMass k = taylorFactorMass (factorRow k) := by
  interval_cases k
  · exact factorMass00_checked
  · exact factorMass01_checked
  · exact factorMass02_checked
  · exact factorMass03_checked
  · exact factorMass04_checked
  · exact factorMass05_checked
  · exact factorMass06_checked
  · exact factorMass07_checked
  · exact factorMass08_checked
  · exact factorMass09_checked
  · exact factorMass10_checked
  · exact factorMass11_checked
  · exact factorMass12_checked
  · exact factorMass13_checked
  · exact factorMass14_checked
  · exact factorMass15_checked
  · exact factorMass16_checked
  · exact factorMass17_checked
  · exact factorMass18_checked
  · exact factorMass19_checked

end
end ErdosOverlap.Native6Grid
