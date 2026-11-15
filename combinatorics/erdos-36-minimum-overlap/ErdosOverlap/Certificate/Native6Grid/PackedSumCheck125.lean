module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows125
public import ErdosOverlap.Certificate.Native6Grid.PackedDots125

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum1000_checked :
    packedSumCheck packedFactorsEven (row1000.map Prod.fst) evenDots1000 641 10 = true := by
  decide +kernel

theorem oddSum1000_checked :
    packedSumCheck packedFactorsOdd (row1000.map Prod.snd) oddDots1000 641 10 = true := by
  decide +kernel

theorem evenSum1001_checked :
    packedSumCheck packedFactorsEven (row1001.map Prod.fst) evenDots1001 641 10 = true := by
  decide +kernel

theorem oddSum1001_checked :
    packedSumCheck packedFactorsOdd (row1001.map Prod.snd) oddDots1001 641 10 = true := by
  decide +kernel

theorem evenSum1002_checked :
    packedSumCheck packedFactorsEven (row1002.map Prod.fst) evenDots1002 641 10 = true := by
  decide +kernel

theorem oddSum1002_checked :
    packedSumCheck packedFactorsOdd (row1002.map Prod.snd) oddDots1002 641 10 = true := by
  decide +kernel

theorem evenSum1003_checked :
    packedSumCheck packedFactorsEven (row1003.map Prod.fst) evenDots1003 641 10 = true := by
  decide +kernel

theorem oddSum1003_checked :
    packedSumCheck packedFactorsOdd (row1003.map Prod.snd) oddDots1003 641 10 = true := by
  decide +kernel

theorem evenSum1004_checked :
    packedSumCheck packedFactorsEven (row1004.map Prod.fst) evenDots1004 641 10 = true := by
  decide +kernel

theorem oddSum1004_checked :
    packedSumCheck packedFactorsOdd (row1004.map Prod.snd) oddDots1004 641 10 = true := by
  decide +kernel

theorem evenSum1005_checked :
    packedSumCheck packedFactorsEven (row1005.map Prod.fst) evenDots1005 641 10 = true := by
  decide +kernel

theorem oddSum1005_checked :
    packedSumCheck packedFactorsOdd (row1005.map Prod.snd) oddDots1005 641 10 = true := by
  decide +kernel

theorem evenSum1006_checked :
    packedSumCheck packedFactorsEven (row1006.map Prod.fst) evenDots1006 641 10 = true := by
  decide +kernel

theorem oddSum1006_checked :
    packedSumCheck packedFactorsOdd (row1006.map Prod.snd) oddDots1006 641 10 = true := by
  decide +kernel

theorem evenSum1007_checked :
    packedSumCheck packedFactorsEven (row1007.map Prod.fst) evenDots1007 641 10 = true := by
  decide +kernel

theorem oddSum1007_checked :
    packedSumCheck packedFactorsOdd (row1007.map Prod.snd) oddDots1007 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
