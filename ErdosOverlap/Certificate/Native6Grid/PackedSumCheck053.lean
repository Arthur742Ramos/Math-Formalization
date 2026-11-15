module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows053
public import ErdosOverlap.Certificate.Native6Grid.PackedDots053

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0424_checked :
    packedSumCheck packedFactorsEven (row0424.map Prod.fst) evenDots0424 641 10 = true := by
  decide +kernel

theorem oddSum0424_checked :
    packedSumCheck packedFactorsOdd (row0424.map Prod.snd) oddDots0424 641 10 = true := by
  decide +kernel

theorem evenSum0425_checked :
    packedSumCheck packedFactorsEven (row0425.map Prod.fst) evenDots0425 641 10 = true := by
  decide +kernel

theorem oddSum0425_checked :
    packedSumCheck packedFactorsOdd (row0425.map Prod.snd) oddDots0425 641 10 = true := by
  decide +kernel

theorem evenSum0426_checked :
    packedSumCheck packedFactorsEven (row0426.map Prod.fst) evenDots0426 641 10 = true := by
  decide +kernel

theorem oddSum0426_checked :
    packedSumCheck packedFactorsOdd (row0426.map Prod.snd) oddDots0426 641 10 = true := by
  decide +kernel

theorem evenSum0427_checked :
    packedSumCheck packedFactorsEven (row0427.map Prod.fst) evenDots0427 641 10 = true := by
  decide +kernel

theorem oddSum0427_checked :
    packedSumCheck packedFactorsOdd (row0427.map Prod.snd) oddDots0427 641 10 = true := by
  decide +kernel

theorem evenSum0428_checked :
    packedSumCheck packedFactorsEven (row0428.map Prod.fst) evenDots0428 641 10 = true := by
  decide +kernel

theorem oddSum0428_checked :
    packedSumCheck packedFactorsOdd (row0428.map Prod.snd) oddDots0428 641 10 = true := by
  decide +kernel

theorem evenSum0429_checked :
    packedSumCheck packedFactorsEven (row0429.map Prod.fst) evenDots0429 641 10 = true := by
  decide +kernel

theorem oddSum0429_checked :
    packedSumCheck packedFactorsOdd (row0429.map Prod.snd) oddDots0429 641 10 = true := by
  decide +kernel

theorem evenSum0430_checked :
    packedSumCheck packedFactorsEven (row0430.map Prod.fst) evenDots0430 641 10 = true := by
  decide +kernel

theorem oddSum0430_checked :
    packedSumCheck packedFactorsOdd (row0430.map Prod.snd) oddDots0430 641 10 = true := by
  decide +kernel

theorem evenSum0431_checked :
    packedSumCheck packedFactorsEven (row0431.map Prod.fst) evenDots0431 641 10 = true := by
  decide +kernel

theorem oddSum0431_checked :
    packedSumCheck packedFactorsOdd (row0431.map Prod.snd) oddDots0431 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
