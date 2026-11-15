module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows015
public import ErdosOverlap.Certificate.Native6Grid.PackedDots015

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0120_checked :
    packedSumCheck packedFactorsEven (row0120.map Prod.fst) evenDots0120 641 10 = true := by
  decide +kernel

theorem oddSum0120_checked :
    packedSumCheck packedFactorsOdd (row0120.map Prod.snd) oddDots0120 641 10 = true := by
  decide +kernel

theorem evenSum0121_checked :
    packedSumCheck packedFactorsEven (row0121.map Prod.fst) evenDots0121 641 10 = true := by
  decide +kernel

theorem oddSum0121_checked :
    packedSumCheck packedFactorsOdd (row0121.map Prod.snd) oddDots0121 641 10 = true := by
  decide +kernel

theorem evenSum0122_checked :
    packedSumCheck packedFactorsEven (row0122.map Prod.fst) evenDots0122 641 10 = true := by
  decide +kernel

theorem oddSum0122_checked :
    packedSumCheck packedFactorsOdd (row0122.map Prod.snd) oddDots0122 641 10 = true := by
  decide +kernel

theorem evenSum0123_checked :
    packedSumCheck packedFactorsEven (row0123.map Prod.fst) evenDots0123 641 10 = true := by
  decide +kernel

theorem oddSum0123_checked :
    packedSumCheck packedFactorsOdd (row0123.map Prod.snd) oddDots0123 641 10 = true := by
  decide +kernel

theorem evenSum0124_checked :
    packedSumCheck packedFactorsEven (row0124.map Prod.fst) evenDots0124 641 10 = true := by
  decide +kernel

theorem oddSum0124_checked :
    packedSumCheck packedFactorsOdd (row0124.map Prod.snd) oddDots0124 641 10 = true := by
  decide +kernel

theorem evenSum0125_checked :
    packedSumCheck packedFactorsEven (row0125.map Prod.fst) evenDots0125 641 10 = true := by
  decide +kernel

theorem oddSum0125_checked :
    packedSumCheck packedFactorsOdd (row0125.map Prod.snd) oddDots0125 641 10 = true := by
  decide +kernel

theorem evenSum0126_checked :
    packedSumCheck packedFactorsEven (row0126.map Prod.fst) evenDots0126 641 10 = true := by
  decide +kernel

theorem oddSum0126_checked :
    packedSumCheck packedFactorsOdd (row0126.map Prod.snd) oddDots0126 641 10 = true := by
  decide +kernel

theorem evenSum0127_checked :
    packedSumCheck packedFactorsEven (row0127.map Prod.fst) evenDots0127 641 10 = true := by
  decide +kernel

theorem oddSum0127_checked :
    packedSumCheck packedFactorsOdd (row0127.map Prod.snd) oddDots0127 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
