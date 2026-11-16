module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows006
public import ErdosOverlap.Certificate.Native6Grid.PackedDots006

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0048_checked :
    packedSumCheck packedFactorsEven (row0048.map Prod.fst) evenDots0048 641 10 = true := by
  decide +kernel

theorem oddSum0048_checked :
    packedSumCheck packedFactorsOdd (row0048.map Prod.snd) oddDots0048 641 10 = true := by
  decide +kernel

theorem evenSum0049_checked :
    packedSumCheck packedFactorsEven (row0049.map Prod.fst) evenDots0049 641 10 = true := by
  decide +kernel

theorem oddSum0049_checked :
    packedSumCheck packedFactorsOdd (row0049.map Prod.snd) oddDots0049 641 10 = true := by
  decide +kernel

theorem evenSum0050_checked :
    packedSumCheck packedFactorsEven (row0050.map Prod.fst) evenDots0050 641 10 = true := by
  decide +kernel

theorem oddSum0050_checked :
    packedSumCheck packedFactorsOdd (row0050.map Prod.snd) oddDots0050 641 10 = true := by
  decide +kernel

theorem evenSum0051_checked :
    packedSumCheck packedFactorsEven (row0051.map Prod.fst) evenDots0051 641 10 = true := by
  decide +kernel

theorem oddSum0051_checked :
    packedSumCheck packedFactorsOdd (row0051.map Prod.snd) oddDots0051 641 10 = true := by
  decide +kernel

theorem evenSum0052_checked :
    packedSumCheck packedFactorsEven (row0052.map Prod.fst) evenDots0052 641 10 = true := by
  decide +kernel

theorem oddSum0052_checked :
    packedSumCheck packedFactorsOdd (row0052.map Prod.snd) oddDots0052 641 10 = true := by
  decide +kernel

theorem evenSum0053_checked :
    packedSumCheck packedFactorsEven (row0053.map Prod.fst) evenDots0053 641 10 = true := by
  decide +kernel

theorem oddSum0053_checked :
    packedSumCheck packedFactorsOdd (row0053.map Prod.snd) oddDots0053 641 10 = true := by
  decide +kernel

theorem evenSum0054_checked :
    packedSumCheck packedFactorsEven (row0054.map Prod.fst) evenDots0054 641 10 = true := by
  decide +kernel

theorem oddSum0054_checked :
    packedSumCheck packedFactorsOdd (row0054.map Prod.snd) oddDots0054 641 10 = true := by
  decide +kernel

theorem evenSum0055_checked :
    packedSumCheck packedFactorsEven (row0055.map Prod.fst) evenDots0055 641 10 = true := by
  decide +kernel

theorem oddSum0055_checked :
    packedSumCheck packedFactorsOdd (row0055.map Prod.snd) oddDots0055 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
