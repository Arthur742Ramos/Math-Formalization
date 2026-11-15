module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows019
public import ErdosOverlap.Certificate.Native6Grid.PackedDots019

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0152_checked :
    packedSumCheck packedFactorsEven (row0152.map Prod.fst) evenDots0152 641 10 = true := by
  decide +kernel

theorem oddSum0152_checked :
    packedSumCheck packedFactorsOdd (row0152.map Prod.snd) oddDots0152 641 10 = true := by
  decide +kernel

theorem evenSum0153_checked :
    packedSumCheck packedFactorsEven (row0153.map Prod.fst) evenDots0153 641 10 = true := by
  decide +kernel

theorem oddSum0153_checked :
    packedSumCheck packedFactorsOdd (row0153.map Prod.snd) oddDots0153 641 10 = true := by
  decide +kernel

theorem evenSum0154_checked :
    packedSumCheck packedFactorsEven (row0154.map Prod.fst) evenDots0154 641 10 = true := by
  decide +kernel

theorem oddSum0154_checked :
    packedSumCheck packedFactorsOdd (row0154.map Prod.snd) oddDots0154 641 10 = true := by
  decide +kernel

theorem evenSum0155_checked :
    packedSumCheck packedFactorsEven (row0155.map Prod.fst) evenDots0155 641 10 = true := by
  decide +kernel

theorem oddSum0155_checked :
    packedSumCheck packedFactorsOdd (row0155.map Prod.snd) oddDots0155 641 10 = true := by
  decide +kernel

theorem evenSum0156_checked :
    packedSumCheck packedFactorsEven (row0156.map Prod.fst) evenDots0156 641 10 = true := by
  decide +kernel

theorem oddSum0156_checked :
    packedSumCheck packedFactorsOdd (row0156.map Prod.snd) oddDots0156 641 10 = true := by
  decide +kernel

theorem evenSum0157_checked :
    packedSumCheck packedFactorsEven (row0157.map Prod.fst) evenDots0157 641 10 = true := by
  decide +kernel

theorem oddSum0157_checked :
    packedSumCheck packedFactorsOdd (row0157.map Prod.snd) oddDots0157 641 10 = true := by
  decide +kernel

theorem evenSum0158_checked :
    packedSumCheck packedFactorsEven (row0158.map Prod.fst) evenDots0158 641 10 = true := by
  decide +kernel

theorem oddSum0158_checked :
    packedSumCheck packedFactorsOdd (row0158.map Prod.snd) oddDots0158 641 10 = true := by
  decide +kernel

theorem evenSum0159_checked :
    packedSumCheck packedFactorsEven (row0159.map Prod.fst) evenDots0159 641 10 = true := by
  decide +kernel

theorem oddSum0159_checked :
    packedSumCheck packedFactorsOdd (row0159.map Prod.snd) oddDots0159 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
