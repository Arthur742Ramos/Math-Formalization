module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows044
public import ErdosOverlap.Certificate.Native6Grid.PackedDots044

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0352_checked :
    packedSumCheck packedFactorsEven (row0352.map Prod.fst) evenDots0352 641 10 = true := by
  decide +kernel

theorem oddSum0352_checked :
    packedSumCheck packedFactorsOdd (row0352.map Prod.snd) oddDots0352 641 10 = true := by
  decide +kernel

theorem evenSum0353_checked :
    packedSumCheck packedFactorsEven (row0353.map Prod.fst) evenDots0353 641 10 = true := by
  decide +kernel

theorem oddSum0353_checked :
    packedSumCheck packedFactorsOdd (row0353.map Prod.snd) oddDots0353 641 10 = true := by
  decide +kernel

theorem evenSum0354_checked :
    packedSumCheck packedFactorsEven (row0354.map Prod.fst) evenDots0354 641 10 = true := by
  decide +kernel

theorem oddSum0354_checked :
    packedSumCheck packedFactorsOdd (row0354.map Prod.snd) oddDots0354 641 10 = true := by
  decide +kernel

theorem evenSum0355_checked :
    packedSumCheck packedFactorsEven (row0355.map Prod.fst) evenDots0355 641 10 = true := by
  decide +kernel

theorem oddSum0355_checked :
    packedSumCheck packedFactorsOdd (row0355.map Prod.snd) oddDots0355 641 10 = true := by
  decide +kernel

theorem evenSum0356_checked :
    packedSumCheck packedFactorsEven (row0356.map Prod.fst) evenDots0356 641 10 = true := by
  decide +kernel

theorem oddSum0356_checked :
    packedSumCheck packedFactorsOdd (row0356.map Prod.snd) oddDots0356 641 10 = true := by
  decide +kernel

theorem evenSum0357_checked :
    packedSumCheck packedFactorsEven (row0357.map Prod.fst) evenDots0357 641 10 = true := by
  decide +kernel

theorem oddSum0357_checked :
    packedSumCheck packedFactorsOdd (row0357.map Prod.snd) oddDots0357 641 10 = true := by
  decide +kernel

theorem evenSum0358_checked :
    packedSumCheck packedFactorsEven (row0358.map Prod.fst) evenDots0358 641 10 = true := by
  decide +kernel

theorem oddSum0358_checked :
    packedSumCheck packedFactorsOdd (row0358.map Prod.snd) oddDots0358 641 10 = true := by
  decide +kernel

theorem evenSum0359_checked :
    packedSumCheck packedFactorsEven (row0359.map Prod.fst) evenDots0359 641 10 = true := by
  decide +kernel

theorem oddSum0359_checked :
    packedSumCheck packedFactorsOdd (row0359.map Prod.snd) oddDots0359 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
