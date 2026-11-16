module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows035
public import ErdosOverlap.Certificate.Native6Grid.PackedDots035

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0280_checked :
    packedSumCheck packedFactorsEven (row0280.map Prod.fst) evenDots0280 641 10 = true := by
  decide +kernel

theorem oddSum0280_checked :
    packedSumCheck packedFactorsOdd (row0280.map Prod.snd) oddDots0280 641 10 = true := by
  decide +kernel

theorem evenSum0281_checked :
    packedSumCheck packedFactorsEven (row0281.map Prod.fst) evenDots0281 641 10 = true := by
  decide +kernel

theorem oddSum0281_checked :
    packedSumCheck packedFactorsOdd (row0281.map Prod.snd) oddDots0281 641 10 = true := by
  decide +kernel

theorem evenSum0282_checked :
    packedSumCheck packedFactorsEven (row0282.map Prod.fst) evenDots0282 641 10 = true := by
  decide +kernel

theorem oddSum0282_checked :
    packedSumCheck packedFactorsOdd (row0282.map Prod.snd) oddDots0282 641 10 = true := by
  decide +kernel

theorem evenSum0283_checked :
    packedSumCheck packedFactorsEven (row0283.map Prod.fst) evenDots0283 641 10 = true := by
  decide +kernel

theorem oddSum0283_checked :
    packedSumCheck packedFactorsOdd (row0283.map Prod.snd) oddDots0283 641 10 = true := by
  decide +kernel

theorem evenSum0284_checked :
    packedSumCheck packedFactorsEven (row0284.map Prod.fst) evenDots0284 641 10 = true := by
  decide +kernel

theorem oddSum0284_checked :
    packedSumCheck packedFactorsOdd (row0284.map Prod.snd) oddDots0284 641 10 = true := by
  decide +kernel

theorem evenSum0285_checked :
    packedSumCheck packedFactorsEven (row0285.map Prod.fst) evenDots0285 641 10 = true := by
  decide +kernel

theorem oddSum0285_checked :
    packedSumCheck packedFactorsOdd (row0285.map Prod.snd) oddDots0285 641 10 = true := by
  decide +kernel

theorem evenSum0286_checked :
    packedSumCheck packedFactorsEven (row0286.map Prod.fst) evenDots0286 641 10 = true := by
  decide +kernel

theorem oddSum0286_checked :
    packedSumCheck packedFactorsOdd (row0286.map Prod.snd) oddDots0286 641 10 = true := by
  decide +kernel

theorem evenSum0287_checked :
    packedSumCheck packedFactorsEven (row0287.map Prod.fst) evenDots0287 641 10 = true := by
  decide +kernel

theorem oddSum0287_checked :
    packedSumCheck packedFactorsOdd (row0287.map Prod.snd) oddDots0287 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
