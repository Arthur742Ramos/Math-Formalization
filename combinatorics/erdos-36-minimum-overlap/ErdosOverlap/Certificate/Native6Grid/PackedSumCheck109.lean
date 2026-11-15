module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows109
public import ErdosOverlap.Certificate.Native6Grid.PackedDots109

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0872_checked :
    packedSumCheck packedFactorsEven (row0872.map Prod.fst) evenDots0872 641 10 = true := by
  decide +kernel

theorem oddSum0872_checked :
    packedSumCheck packedFactorsOdd (row0872.map Prod.snd) oddDots0872 641 10 = true := by
  decide +kernel

theorem evenSum0873_checked :
    packedSumCheck packedFactorsEven (row0873.map Prod.fst) evenDots0873 641 10 = true := by
  decide +kernel

theorem oddSum0873_checked :
    packedSumCheck packedFactorsOdd (row0873.map Prod.snd) oddDots0873 641 10 = true := by
  decide +kernel

theorem evenSum0874_checked :
    packedSumCheck packedFactorsEven (row0874.map Prod.fst) evenDots0874 641 10 = true := by
  decide +kernel

theorem oddSum0874_checked :
    packedSumCheck packedFactorsOdd (row0874.map Prod.snd) oddDots0874 641 10 = true := by
  decide +kernel

theorem evenSum0875_checked :
    packedSumCheck packedFactorsEven (row0875.map Prod.fst) evenDots0875 641 10 = true := by
  decide +kernel

theorem oddSum0875_checked :
    packedSumCheck packedFactorsOdd (row0875.map Prod.snd) oddDots0875 641 10 = true := by
  decide +kernel

theorem evenSum0876_checked :
    packedSumCheck packedFactorsEven (row0876.map Prod.fst) evenDots0876 641 10 = true := by
  decide +kernel

theorem oddSum0876_checked :
    packedSumCheck packedFactorsOdd (row0876.map Prod.snd) oddDots0876 641 10 = true := by
  decide +kernel

theorem evenSum0877_checked :
    packedSumCheck packedFactorsEven (row0877.map Prod.fst) evenDots0877 641 10 = true := by
  decide +kernel

theorem oddSum0877_checked :
    packedSumCheck packedFactorsOdd (row0877.map Prod.snd) oddDots0877 641 10 = true := by
  decide +kernel

theorem evenSum0878_checked :
    packedSumCheck packedFactorsEven (row0878.map Prod.fst) evenDots0878 641 10 = true := by
  decide +kernel

theorem oddSum0878_checked :
    packedSumCheck packedFactorsOdd (row0878.map Prod.snd) oddDots0878 641 10 = true := by
  decide +kernel

theorem evenSum0879_checked :
    packedSumCheck packedFactorsEven (row0879.map Prod.fst) evenDots0879 641 10 = true := by
  decide +kernel

theorem oddSum0879_checked :
    packedSumCheck packedFactorsOdd (row0879.map Prod.snd) oddDots0879 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
