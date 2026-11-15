module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows051
public import ErdosOverlap.Certificate.Native6Grid.PackedDots051

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0408_checked :
    packedSumCheck packedFactorsEven (row0408.map Prod.fst) evenDots0408 641 10 = true := by
  decide +kernel

theorem oddSum0408_checked :
    packedSumCheck packedFactorsOdd (row0408.map Prod.snd) oddDots0408 641 10 = true := by
  decide +kernel

theorem evenSum0409_checked :
    packedSumCheck packedFactorsEven (row0409.map Prod.fst) evenDots0409 641 10 = true := by
  decide +kernel

theorem oddSum0409_checked :
    packedSumCheck packedFactorsOdd (row0409.map Prod.snd) oddDots0409 641 10 = true := by
  decide +kernel

theorem evenSum0410_checked :
    packedSumCheck packedFactorsEven (row0410.map Prod.fst) evenDots0410 641 10 = true := by
  decide +kernel

theorem oddSum0410_checked :
    packedSumCheck packedFactorsOdd (row0410.map Prod.snd) oddDots0410 641 10 = true := by
  decide +kernel

theorem evenSum0411_checked :
    packedSumCheck packedFactorsEven (row0411.map Prod.fst) evenDots0411 641 10 = true := by
  decide +kernel

theorem oddSum0411_checked :
    packedSumCheck packedFactorsOdd (row0411.map Prod.snd) oddDots0411 641 10 = true := by
  decide +kernel

theorem evenSum0412_checked :
    packedSumCheck packedFactorsEven (row0412.map Prod.fst) evenDots0412 641 10 = true := by
  decide +kernel

theorem oddSum0412_checked :
    packedSumCheck packedFactorsOdd (row0412.map Prod.snd) oddDots0412 641 10 = true := by
  decide +kernel

theorem evenSum0413_checked :
    packedSumCheck packedFactorsEven (row0413.map Prod.fst) evenDots0413 641 10 = true := by
  decide +kernel

theorem oddSum0413_checked :
    packedSumCheck packedFactorsOdd (row0413.map Prod.snd) oddDots0413 641 10 = true := by
  decide +kernel

theorem evenSum0414_checked :
    packedSumCheck packedFactorsEven (row0414.map Prod.fst) evenDots0414 641 10 = true := by
  decide +kernel

theorem oddSum0414_checked :
    packedSumCheck packedFactorsOdd (row0414.map Prod.snd) oddDots0414 641 10 = true := by
  decide +kernel

theorem evenSum0415_checked :
    packedSumCheck packedFactorsEven (row0415.map Prod.fst) evenDots0415 641 10 = true := by
  decide +kernel

theorem oddSum0415_checked :
    packedSumCheck packedFactorsOdd (row0415.map Prod.snd) oddDots0415 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
