module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows126
public import ErdosOverlap.Certificate.Native6Grid.PackedDots126

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum1008_checked :
    packedSumCheck packedFactorsEven (row1008.map Prod.fst) evenDots1008 641 10 = true := by
  decide +kernel

theorem oddSum1008_checked :
    packedSumCheck packedFactorsOdd (row1008.map Prod.snd) oddDots1008 641 10 = true := by
  decide +kernel

theorem evenSum1009_checked :
    packedSumCheck packedFactorsEven (row1009.map Prod.fst) evenDots1009 641 10 = true := by
  decide +kernel

theorem oddSum1009_checked :
    packedSumCheck packedFactorsOdd (row1009.map Prod.snd) oddDots1009 641 10 = true := by
  decide +kernel

theorem evenSum1010_checked :
    packedSumCheck packedFactorsEven (row1010.map Prod.fst) evenDots1010 641 10 = true := by
  decide +kernel

theorem oddSum1010_checked :
    packedSumCheck packedFactorsOdd (row1010.map Prod.snd) oddDots1010 641 10 = true := by
  decide +kernel

theorem evenSum1011_checked :
    packedSumCheck packedFactorsEven (row1011.map Prod.fst) evenDots1011 641 10 = true := by
  decide +kernel

theorem oddSum1011_checked :
    packedSumCheck packedFactorsOdd (row1011.map Prod.snd) oddDots1011 641 10 = true := by
  decide +kernel

theorem evenSum1012_checked :
    packedSumCheck packedFactorsEven (row1012.map Prod.fst) evenDots1012 641 10 = true := by
  decide +kernel

theorem oddSum1012_checked :
    packedSumCheck packedFactorsOdd (row1012.map Prod.snd) oddDots1012 641 10 = true := by
  decide +kernel

theorem evenSum1013_checked :
    packedSumCheck packedFactorsEven (row1013.map Prod.fst) evenDots1013 641 10 = true := by
  decide +kernel

theorem oddSum1013_checked :
    packedSumCheck packedFactorsOdd (row1013.map Prod.snd) oddDots1013 641 10 = true := by
  decide +kernel

theorem evenSum1014_checked :
    packedSumCheck packedFactorsEven (row1014.map Prod.fst) evenDots1014 641 10 = true := by
  decide +kernel

theorem oddSum1014_checked :
    packedSumCheck packedFactorsOdd (row1014.map Prod.snd) oddDots1014 641 10 = true := by
  decide +kernel

theorem evenSum1015_checked :
    packedSumCheck packedFactorsEven (row1015.map Prod.fst) evenDots1015 641 10 = true := by
  decide +kernel

theorem oddSum1015_checked :
    packedSumCheck packedFactorsOdd (row1015.map Prod.snd) oddDots1015 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
