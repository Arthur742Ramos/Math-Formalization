module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows036
public import ErdosOverlap.Certificate.Native6Grid.PackedDots036

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0288_checked :
    packedSumCheck packedFactorsEven (row0288.map Prod.fst) evenDots0288 641 10 = true := by
  decide +kernel

theorem oddSum0288_checked :
    packedSumCheck packedFactorsOdd (row0288.map Prod.snd) oddDots0288 641 10 = true := by
  decide +kernel

theorem evenSum0289_checked :
    packedSumCheck packedFactorsEven (row0289.map Prod.fst) evenDots0289 641 10 = true := by
  decide +kernel

theorem oddSum0289_checked :
    packedSumCheck packedFactorsOdd (row0289.map Prod.snd) oddDots0289 641 10 = true := by
  decide +kernel

theorem evenSum0290_checked :
    packedSumCheck packedFactorsEven (row0290.map Prod.fst) evenDots0290 641 10 = true := by
  decide +kernel

theorem oddSum0290_checked :
    packedSumCheck packedFactorsOdd (row0290.map Prod.snd) oddDots0290 641 10 = true := by
  decide +kernel

theorem evenSum0291_checked :
    packedSumCheck packedFactorsEven (row0291.map Prod.fst) evenDots0291 641 10 = true := by
  decide +kernel

theorem oddSum0291_checked :
    packedSumCheck packedFactorsOdd (row0291.map Prod.snd) oddDots0291 641 10 = true := by
  decide +kernel

theorem evenSum0292_checked :
    packedSumCheck packedFactorsEven (row0292.map Prod.fst) evenDots0292 641 10 = true := by
  decide +kernel

theorem oddSum0292_checked :
    packedSumCheck packedFactorsOdd (row0292.map Prod.snd) oddDots0292 641 10 = true := by
  decide +kernel

theorem evenSum0293_checked :
    packedSumCheck packedFactorsEven (row0293.map Prod.fst) evenDots0293 641 10 = true := by
  decide +kernel

theorem oddSum0293_checked :
    packedSumCheck packedFactorsOdd (row0293.map Prod.snd) oddDots0293 641 10 = true := by
  decide +kernel

theorem evenSum0294_checked :
    packedSumCheck packedFactorsEven (row0294.map Prod.fst) evenDots0294 641 10 = true := by
  decide +kernel

theorem oddSum0294_checked :
    packedSumCheck packedFactorsOdd (row0294.map Prod.snd) oddDots0294 641 10 = true := by
  decide +kernel

theorem evenSum0295_checked :
    packedSumCheck packedFactorsEven (row0295.map Prod.fst) evenDots0295 641 10 = true := by
  decide +kernel

theorem oddSum0295_checked :
    packedSumCheck packedFactorsOdd (row0295.map Prod.snd) oddDots0295 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
