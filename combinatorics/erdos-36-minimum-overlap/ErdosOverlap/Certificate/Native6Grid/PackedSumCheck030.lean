module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows030
public import ErdosOverlap.Certificate.Native6Grid.PackedDots030

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0240_checked :
    packedSumCheck packedFactorsEven (row0240.map Prod.fst) evenDots0240 641 10 = true := by
  decide +kernel

theorem oddSum0240_checked :
    packedSumCheck packedFactorsOdd (row0240.map Prod.snd) oddDots0240 641 10 = true := by
  decide +kernel

theorem evenSum0241_checked :
    packedSumCheck packedFactorsEven (row0241.map Prod.fst) evenDots0241 641 10 = true := by
  decide +kernel

theorem oddSum0241_checked :
    packedSumCheck packedFactorsOdd (row0241.map Prod.snd) oddDots0241 641 10 = true := by
  decide +kernel

theorem evenSum0242_checked :
    packedSumCheck packedFactorsEven (row0242.map Prod.fst) evenDots0242 641 10 = true := by
  decide +kernel

theorem oddSum0242_checked :
    packedSumCheck packedFactorsOdd (row0242.map Prod.snd) oddDots0242 641 10 = true := by
  decide +kernel

theorem evenSum0243_checked :
    packedSumCheck packedFactorsEven (row0243.map Prod.fst) evenDots0243 641 10 = true := by
  decide +kernel

theorem oddSum0243_checked :
    packedSumCheck packedFactorsOdd (row0243.map Prod.snd) oddDots0243 641 10 = true := by
  decide +kernel

theorem evenSum0244_checked :
    packedSumCheck packedFactorsEven (row0244.map Prod.fst) evenDots0244 641 10 = true := by
  decide +kernel

theorem oddSum0244_checked :
    packedSumCheck packedFactorsOdd (row0244.map Prod.snd) oddDots0244 641 10 = true := by
  decide +kernel

theorem evenSum0245_checked :
    packedSumCheck packedFactorsEven (row0245.map Prod.fst) evenDots0245 641 10 = true := by
  decide +kernel

theorem oddSum0245_checked :
    packedSumCheck packedFactorsOdd (row0245.map Prod.snd) oddDots0245 641 10 = true := by
  decide +kernel

theorem evenSum0246_checked :
    packedSumCheck packedFactorsEven (row0246.map Prod.fst) evenDots0246 641 10 = true := by
  decide +kernel

theorem oddSum0246_checked :
    packedSumCheck packedFactorsOdd (row0246.map Prod.snd) oddDots0246 641 10 = true := by
  decide +kernel

theorem evenSum0247_checked :
    packedSumCheck packedFactorsEven (row0247.map Prod.fst) evenDots0247 641 10 = true := by
  decide +kernel

theorem oddSum0247_checked :
    packedSumCheck packedFactorsOdd (row0247.map Prod.snd) oddDots0247 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
