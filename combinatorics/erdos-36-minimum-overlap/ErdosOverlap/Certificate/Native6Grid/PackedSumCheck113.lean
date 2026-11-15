module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows113
public import ErdosOverlap.Certificate.Native6Grid.PackedDots113

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0904_checked :
    packedSumCheck packedFactorsEven (row0904.map Prod.fst) evenDots0904 641 10 = true := by
  decide +kernel

theorem oddSum0904_checked :
    packedSumCheck packedFactorsOdd (row0904.map Prod.snd) oddDots0904 641 10 = true := by
  decide +kernel

theorem evenSum0905_checked :
    packedSumCheck packedFactorsEven (row0905.map Prod.fst) evenDots0905 641 10 = true := by
  decide +kernel

theorem oddSum0905_checked :
    packedSumCheck packedFactorsOdd (row0905.map Prod.snd) oddDots0905 641 10 = true := by
  decide +kernel

theorem evenSum0906_checked :
    packedSumCheck packedFactorsEven (row0906.map Prod.fst) evenDots0906 641 10 = true := by
  decide +kernel

theorem oddSum0906_checked :
    packedSumCheck packedFactorsOdd (row0906.map Prod.snd) oddDots0906 641 10 = true := by
  decide +kernel

theorem evenSum0907_checked :
    packedSumCheck packedFactorsEven (row0907.map Prod.fst) evenDots0907 641 10 = true := by
  decide +kernel

theorem oddSum0907_checked :
    packedSumCheck packedFactorsOdd (row0907.map Prod.snd) oddDots0907 641 10 = true := by
  decide +kernel

theorem evenSum0908_checked :
    packedSumCheck packedFactorsEven (row0908.map Prod.fst) evenDots0908 641 10 = true := by
  decide +kernel

theorem oddSum0908_checked :
    packedSumCheck packedFactorsOdd (row0908.map Prod.snd) oddDots0908 641 10 = true := by
  decide +kernel

theorem evenSum0909_checked :
    packedSumCheck packedFactorsEven (row0909.map Prod.fst) evenDots0909 641 10 = true := by
  decide +kernel

theorem oddSum0909_checked :
    packedSumCheck packedFactorsOdd (row0909.map Prod.snd) oddDots0909 641 10 = true := by
  decide +kernel

theorem evenSum0910_checked :
    packedSumCheck packedFactorsEven (row0910.map Prod.fst) evenDots0910 641 10 = true := by
  decide +kernel

theorem oddSum0910_checked :
    packedSumCheck packedFactorsOdd (row0910.map Prod.snd) oddDots0910 641 10 = true := by
  decide +kernel

theorem evenSum0911_checked :
    packedSumCheck packedFactorsEven (row0911.map Prod.fst) evenDots0911 641 10 = true := by
  decide +kernel

theorem oddSum0911_checked :
    packedSumCheck packedFactorsOdd (row0911.map Prod.snd) oddDots0911 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
