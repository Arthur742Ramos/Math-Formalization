module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows066
public import ErdosOverlap.Certificate.Native6Grid.PackedDots066

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0528_checked :
    packedSumCheck packedFactorsEven (row0528.map Prod.fst) evenDots0528 641 10 = true := by
  decide +kernel

theorem oddSum0528_checked :
    packedSumCheck packedFactorsOdd (row0528.map Prod.snd) oddDots0528 641 10 = true := by
  decide +kernel

theorem evenSum0529_checked :
    packedSumCheck packedFactorsEven (row0529.map Prod.fst) evenDots0529 641 10 = true := by
  decide +kernel

theorem oddSum0529_checked :
    packedSumCheck packedFactorsOdd (row0529.map Prod.snd) oddDots0529 641 10 = true := by
  decide +kernel

theorem evenSum0530_checked :
    packedSumCheck packedFactorsEven (row0530.map Prod.fst) evenDots0530 641 10 = true := by
  decide +kernel

theorem oddSum0530_checked :
    packedSumCheck packedFactorsOdd (row0530.map Prod.snd) oddDots0530 641 10 = true := by
  decide +kernel

theorem evenSum0531_checked :
    packedSumCheck packedFactorsEven (row0531.map Prod.fst) evenDots0531 641 10 = true := by
  decide +kernel

theorem oddSum0531_checked :
    packedSumCheck packedFactorsOdd (row0531.map Prod.snd) oddDots0531 641 10 = true := by
  decide +kernel

theorem evenSum0532_checked :
    packedSumCheck packedFactorsEven (row0532.map Prod.fst) evenDots0532 641 10 = true := by
  decide +kernel

theorem oddSum0532_checked :
    packedSumCheck packedFactorsOdd (row0532.map Prod.snd) oddDots0532 641 10 = true := by
  decide +kernel

theorem evenSum0533_checked :
    packedSumCheck packedFactorsEven (row0533.map Prod.fst) evenDots0533 641 10 = true := by
  decide +kernel

theorem oddSum0533_checked :
    packedSumCheck packedFactorsOdd (row0533.map Prod.snd) oddDots0533 641 10 = true := by
  decide +kernel

theorem evenSum0534_checked :
    packedSumCheck packedFactorsEven (row0534.map Prod.fst) evenDots0534 641 10 = true := by
  decide +kernel

theorem oddSum0534_checked :
    packedSumCheck packedFactorsOdd (row0534.map Prod.snd) oddDots0534 641 10 = true := by
  decide +kernel

theorem evenSum0535_checked :
    packedSumCheck packedFactorsEven (row0535.map Prod.fst) evenDots0535 641 10 = true := by
  decide +kernel

theorem oddSum0535_checked :
    packedSumCheck packedFactorsOdd (row0535.map Prod.snd) oddDots0535 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
