module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows054
public import ErdosOverlap.Certificate.Native6Grid.PackedDots054

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0432_checked :
    packedSumCheck packedFactorsEven (row0432.map Prod.fst) evenDots0432 641 10 = true := by
  decide +kernel

theorem oddSum0432_checked :
    packedSumCheck packedFactorsOdd (row0432.map Prod.snd) oddDots0432 641 10 = true := by
  decide +kernel

theorem evenSum0433_checked :
    packedSumCheck packedFactorsEven (row0433.map Prod.fst) evenDots0433 641 10 = true := by
  decide +kernel

theorem oddSum0433_checked :
    packedSumCheck packedFactorsOdd (row0433.map Prod.snd) oddDots0433 641 10 = true := by
  decide +kernel

theorem evenSum0434_checked :
    packedSumCheck packedFactorsEven (row0434.map Prod.fst) evenDots0434 641 10 = true := by
  decide +kernel

theorem oddSum0434_checked :
    packedSumCheck packedFactorsOdd (row0434.map Prod.snd) oddDots0434 641 10 = true := by
  decide +kernel

theorem evenSum0435_checked :
    packedSumCheck packedFactorsEven (row0435.map Prod.fst) evenDots0435 641 10 = true := by
  decide +kernel

theorem oddSum0435_checked :
    packedSumCheck packedFactorsOdd (row0435.map Prod.snd) oddDots0435 641 10 = true := by
  decide +kernel

theorem evenSum0436_checked :
    packedSumCheck packedFactorsEven (row0436.map Prod.fst) evenDots0436 641 10 = true := by
  decide +kernel

theorem oddSum0436_checked :
    packedSumCheck packedFactorsOdd (row0436.map Prod.snd) oddDots0436 641 10 = true := by
  decide +kernel

theorem evenSum0437_checked :
    packedSumCheck packedFactorsEven (row0437.map Prod.fst) evenDots0437 641 10 = true := by
  decide +kernel

theorem oddSum0437_checked :
    packedSumCheck packedFactorsOdd (row0437.map Prod.snd) oddDots0437 641 10 = true := by
  decide +kernel

theorem evenSum0438_checked :
    packedSumCheck packedFactorsEven (row0438.map Prod.fst) evenDots0438 641 10 = true := by
  decide +kernel

theorem oddSum0438_checked :
    packedSumCheck packedFactorsOdd (row0438.map Prod.snd) oddDots0438 641 10 = true := by
  decide +kernel

theorem evenSum0439_checked :
    packedSumCheck packedFactorsEven (row0439.map Prod.fst) evenDots0439 641 10 = true := by
  decide +kernel

theorem oddSum0439_checked :
    packedSumCheck packedFactorsOdd (row0439.map Prod.snd) oddDots0439 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
