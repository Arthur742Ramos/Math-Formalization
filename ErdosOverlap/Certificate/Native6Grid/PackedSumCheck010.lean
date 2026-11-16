module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows010
public import ErdosOverlap.Certificate.Native6Grid.PackedDots010

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0080_checked :
    packedSumCheck packedFactorsEven (row0080.map Prod.fst) evenDots0080 641 10 = true := by
  decide +kernel

theorem oddSum0080_checked :
    packedSumCheck packedFactorsOdd (row0080.map Prod.snd) oddDots0080 641 10 = true := by
  decide +kernel

theorem evenSum0081_checked :
    packedSumCheck packedFactorsEven (row0081.map Prod.fst) evenDots0081 641 10 = true := by
  decide +kernel

theorem oddSum0081_checked :
    packedSumCheck packedFactorsOdd (row0081.map Prod.snd) oddDots0081 641 10 = true := by
  decide +kernel

theorem evenSum0082_checked :
    packedSumCheck packedFactorsEven (row0082.map Prod.fst) evenDots0082 641 10 = true := by
  decide +kernel

theorem oddSum0082_checked :
    packedSumCheck packedFactorsOdd (row0082.map Prod.snd) oddDots0082 641 10 = true := by
  decide +kernel

theorem evenSum0083_checked :
    packedSumCheck packedFactorsEven (row0083.map Prod.fst) evenDots0083 641 10 = true := by
  decide +kernel

theorem oddSum0083_checked :
    packedSumCheck packedFactorsOdd (row0083.map Prod.snd) oddDots0083 641 10 = true := by
  decide +kernel

theorem evenSum0084_checked :
    packedSumCheck packedFactorsEven (row0084.map Prod.fst) evenDots0084 641 10 = true := by
  decide +kernel

theorem oddSum0084_checked :
    packedSumCheck packedFactorsOdd (row0084.map Prod.snd) oddDots0084 641 10 = true := by
  decide +kernel

theorem evenSum0085_checked :
    packedSumCheck packedFactorsEven (row0085.map Prod.fst) evenDots0085 641 10 = true := by
  decide +kernel

theorem oddSum0085_checked :
    packedSumCheck packedFactorsOdd (row0085.map Prod.snd) oddDots0085 641 10 = true := by
  decide +kernel

theorem evenSum0086_checked :
    packedSumCheck packedFactorsEven (row0086.map Prod.fst) evenDots0086 641 10 = true := by
  decide +kernel

theorem oddSum0086_checked :
    packedSumCheck packedFactorsOdd (row0086.map Prod.snd) oddDots0086 641 10 = true := by
  decide +kernel

theorem evenSum0087_checked :
    packedSumCheck packedFactorsEven (row0087.map Prod.fst) evenDots0087 641 10 = true := by
  decide +kernel

theorem oddSum0087_checked :
    packedSumCheck packedFactorsOdd (row0087.map Prod.snd) oddDots0087 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
