module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows043
public import ErdosOverlap.Certificate.Native6Grid.PackedDots043

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0344_checked :
    packedSumCheck packedFactorsEven (row0344.map Prod.fst) evenDots0344 641 10 = true := by
  decide +kernel

theorem oddSum0344_checked :
    packedSumCheck packedFactorsOdd (row0344.map Prod.snd) oddDots0344 641 10 = true := by
  decide +kernel

theorem evenSum0345_checked :
    packedSumCheck packedFactorsEven (row0345.map Prod.fst) evenDots0345 641 10 = true := by
  decide +kernel

theorem oddSum0345_checked :
    packedSumCheck packedFactorsOdd (row0345.map Prod.snd) oddDots0345 641 10 = true := by
  decide +kernel

theorem evenSum0346_checked :
    packedSumCheck packedFactorsEven (row0346.map Prod.fst) evenDots0346 641 10 = true := by
  decide +kernel

theorem oddSum0346_checked :
    packedSumCheck packedFactorsOdd (row0346.map Prod.snd) oddDots0346 641 10 = true := by
  decide +kernel

theorem evenSum0347_checked :
    packedSumCheck packedFactorsEven (row0347.map Prod.fst) evenDots0347 641 10 = true := by
  decide +kernel

theorem oddSum0347_checked :
    packedSumCheck packedFactorsOdd (row0347.map Prod.snd) oddDots0347 641 10 = true := by
  decide +kernel

theorem evenSum0348_checked :
    packedSumCheck packedFactorsEven (row0348.map Prod.fst) evenDots0348 641 10 = true := by
  decide +kernel

theorem oddSum0348_checked :
    packedSumCheck packedFactorsOdd (row0348.map Prod.snd) oddDots0348 641 10 = true := by
  decide +kernel

theorem evenSum0349_checked :
    packedSumCheck packedFactorsEven (row0349.map Prod.fst) evenDots0349 641 10 = true := by
  decide +kernel

theorem oddSum0349_checked :
    packedSumCheck packedFactorsOdd (row0349.map Prod.snd) oddDots0349 641 10 = true := by
  decide +kernel

theorem evenSum0350_checked :
    packedSumCheck packedFactorsEven (row0350.map Prod.fst) evenDots0350 641 10 = true := by
  decide +kernel

theorem oddSum0350_checked :
    packedSumCheck packedFactorsOdd (row0350.map Prod.snd) oddDots0350 641 10 = true := by
  decide +kernel

theorem evenSum0351_checked :
    packedSumCheck packedFactorsEven (row0351.map Prod.fst) evenDots0351 641 10 = true := by
  decide +kernel

theorem oddSum0351_checked :
    packedSumCheck packedFactorsOdd (row0351.map Prod.snd) oddDots0351 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
