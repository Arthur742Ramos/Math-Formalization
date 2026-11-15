module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows009
public import ErdosOverlap.Certificate.Native6Grid.PackedDots009

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0072_checked :
    packedSumCheck packedFactorsEven (row0072.map Prod.fst) evenDots0072 641 10 = true := by
  decide +kernel

theorem oddSum0072_checked :
    packedSumCheck packedFactorsOdd (row0072.map Prod.snd) oddDots0072 641 10 = true := by
  decide +kernel

theorem evenSum0073_checked :
    packedSumCheck packedFactorsEven (row0073.map Prod.fst) evenDots0073 641 10 = true := by
  decide +kernel

theorem oddSum0073_checked :
    packedSumCheck packedFactorsOdd (row0073.map Prod.snd) oddDots0073 641 10 = true := by
  decide +kernel

theorem evenSum0074_checked :
    packedSumCheck packedFactorsEven (row0074.map Prod.fst) evenDots0074 641 10 = true := by
  decide +kernel

theorem oddSum0074_checked :
    packedSumCheck packedFactorsOdd (row0074.map Prod.snd) oddDots0074 641 10 = true := by
  decide +kernel

theorem evenSum0075_checked :
    packedSumCheck packedFactorsEven (row0075.map Prod.fst) evenDots0075 641 10 = true := by
  decide +kernel

theorem oddSum0075_checked :
    packedSumCheck packedFactorsOdd (row0075.map Prod.snd) oddDots0075 641 10 = true := by
  decide +kernel

theorem evenSum0076_checked :
    packedSumCheck packedFactorsEven (row0076.map Prod.fst) evenDots0076 641 10 = true := by
  decide +kernel

theorem oddSum0076_checked :
    packedSumCheck packedFactorsOdd (row0076.map Prod.snd) oddDots0076 641 10 = true := by
  decide +kernel

theorem evenSum0077_checked :
    packedSumCheck packedFactorsEven (row0077.map Prod.fst) evenDots0077 641 10 = true := by
  decide +kernel

theorem oddSum0077_checked :
    packedSumCheck packedFactorsOdd (row0077.map Prod.snd) oddDots0077 641 10 = true := by
  decide +kernel

theorem evenSum0078_checked :
    packedSumCheck packedFactorsEven (row0078.map Prod.fst) evenDots0078 641 10 = true := by
  decide +kernel

theorem oddSum0078_checked :
    packedSumCheck packedFactorsOdd (row0078.map Prod.snd) oddDots0078 641 10 = true := by
  decide +kernel

theorem evenSum0079_checked :
    packedSumCheck packedFactorsEven (row0079.map Prod.fst) evenDots0079 641 10 = true := by
  decide +kernel

theorem oddSum0079_checked :
    packedSumCheck packedFactorsOdd (row0079.map Prod.snd) oddDots0079 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
