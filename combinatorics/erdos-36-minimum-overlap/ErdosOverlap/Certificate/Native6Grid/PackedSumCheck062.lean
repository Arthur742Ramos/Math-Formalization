module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows062
public import ErdosOverlap.Certificate.Native6Grid.PackedDots062

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0496_checked :
    packedSumCheck packedFactorsEven (row0496.map Prod.fst) evenDots0496 641 10 = true := by
  decide +kernel

theorem oddSum0496_checked :
    packedSumCheck packedFactorsOdd (row0496.map Prod.snd) oddDots0496 641 10 = true := by
  decide +kernel

theorem evenSum0497_checked :
    packedSumCheck packedFactorsEven (row0497.map Prod.fst) evenDots0497 641 10 = true := by
  decide +kernel

theorem oddSum0497_checked :
    packedSumCheck packedFactorsOdd (row0497.map Prod.snd) oddDots0497 641 10 = true := by
  decide +kernel

theorem evenSum0498_checked :
    packedSumCheck packedFactorsEven (row0498.map Prod.fst) evenDots0498 641 10 = true := by
  decide +kernel

theorem oddSum0498_checked :
    packedSumCheck packedFactorsOdd (row0498.map Prod.snd) oddDots0498 641 10 = true := by
  decide +kernel

theorem evenSum0499_checked :
    packedSumCheck packedFactorsEven (row0499.map Prod.fst) evenDots0499 641 10 = true := by
  decide +kernel

theorem oddSum0499_checked :
    packedSumCheck packedFactorsOdd (row0499.map Prod.snd) oddDots0499 641 10 = true := by
  decide +kernel

theorem evenSum0500_checked :
    packedSumCheck packedFactorsEven (row0500.map Prod.fst) evenDots0500 641 10 = true := by
  decide +kernel

theorem oddSum0500_checked :
    packedSumCheck packedFactorsOdd (row0500.map Prod.snd) oddDots0500 641 10 = true := by
  decide +kernel

theorem evenSum0501_checked :
    packedSumCheck packedFactorsEven (row0501.map Prod.fst) evenDots0501 641 10 = true := by
  decide +kernel

theorem oddSum0501_checked :
    packedSumCheck packedFactorsOdd (row0501.map Prod.snd) oddDots0501 641 10 = true := by
  decide +kernel

theorem evenSum0502_checked :
    packedSumCheck packedFactorsEven (row0502.map Prod.fst) evenDots0502 641 10 = true := by
  decide +kernel

theorem oddSum0502_checked :
    packedSumCheck packedFactorsOdd (row0502.map Prod.snd) oddDots0502 641 10 = true := by
  decide +kernel

theorem evenSum0503_checked :
    packedSumCheck packedFactorsEven (row0503.map Prod.fst) evenDots0503 641 10 = true := by
  decide +kernel

theorem oddSum0503_checked :
    packedSumCheck packedFactorsOdd (row0503.map Prod.snd) oddDots0503 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
