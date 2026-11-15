module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows012
public import ErdosOverlap.Certificate.Native6Grid.PackedDots012

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0096_checked :
    packedSumCheck packedFactorsEven (row0096.map Prod.fst) evenDots0096 641 10 = true := by
  decide +kernel

theorem oddSum0096_checked :
    packedSumCheck packedFactorsOdd (row0096.map Prod.snd) oddDots0096 641 10 = true := by
  decide +kernel

theorem evenSum0097_checked :
    packedSumCheck packedFactorsEven (row0097.map Prod.fst) evenDots0097 641 10 = true := by
  decide +kernel

theorem oddSum0097_checked :
    packedSumCheck packedFactorsOdd (row0097.map Prod.snd) oddDots0097 641 10 = true := by
  decide +kernel

theorem evenSum0098_checked :
    packedSumCheck packedFactorsEven (row0098.map Prod.fst) evenDots0098 641 10 = true := by
  decide +kernel

theorem oddSum0098_checked :
    packedSumCheck packedFactorsOdd (row0098.map Prod.snd) oddDots0098 641 10 = true := by
  decide +kernel

theorem evenSum0099_checked :
    packedSumCheck packedFactorsEven (row0099.map Prod.fst) evenDots0099 641 10 = true := by
  decide +kernel

theorem oddSum0099_checked :
    packedSumCheck packedFactorsOdd (row0099.map Prod.snd) oddDots0099 641 10 = true := by
  decide +kernel

theorem evenSum0100_checked :
    packedSumCheck packedFactorsEven (row0100.map Prod.fst) evenDots0100 641 10 = true := by
  decide +kernel

theorem oddSum0100_checked :
    packedSumCheck packedFactorsOdd (row0100.map Prod.snd) oddDots0100 641 10 = true := by
  decide +kernel

theorem evenSum0101_checked :
    packedSumCheck packedFactorsEven (row0101.map Prod.fst) evenDots0101 641 10 = true := by
  decide +kernel

theorem oddSum0101_checked :
    packedSumCheck packedFactorsOdd (row0101.map Prod.snd) oddDots0101 641 10 = true := by
  decide +kernel

theorem evenSum0102_checked :
    packedSumCheck packedFactorsEven (row0102.map Prod.fst) evenDots0102 641 10 = true := by
  decide +kernel

theorem oddSum0102_checked :
    packedSumCheck packedFactorsOdd (row0102.map Prod.snd) oddDots0102 641 10 = true := by
  decide +kernel

theorem evenSum0103_checked :
    packedSumCheck packedFactorsEven (row0103.map Prod.fst) evenDots0103 641 10 = true := by
  decide +kernel

theorem oddSum0103_checked :
    packedSumCheck packedFactorsOdd (row0103.map Prod.snd) oddDots0103 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
