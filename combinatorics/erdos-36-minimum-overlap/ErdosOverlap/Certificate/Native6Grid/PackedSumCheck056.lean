module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows056
public import ErdosOverlap.Certificate.Native6Grid.PackedDots056

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0448_checked :
    packedSumCheck packedFactorsEven (row0448.map Prod.fst) evenDots0448 641 10 = true := by
  decide +kernel

theorem oddSum0448_checked :
    packedSumCheck packedFactorsOdd (row0448.map Prod.snd) oddDots0448 641 10 = true := by
  decide +kernel

theorem evenSum0449_checked :
    packedSumCheck packedFactorsEven (row0449.map Prod.fst) evenDots0449 641 10 = true := by
  decide +kernel

theorem oddSum0449_checked :
    packedSumCheck packedFactorsOdd (row0449.map Prod.snd) oddDots0449 641 10 = true := by
  decide +kernel

theorem evenSum0450_checked :
    packedSumCheck packedFactorsEven (row0450.map Prod.fst) evenDots0450 641 10 = true := by
  decide +kernel

theorem oddSum0450_checked :
    packedSumCheck packedFactorsOdd (row0450.map Prod.snd) oddDots0450 641 10 = true := by
  decide +kernel

theorem evenSum0451_checked :
    packedSumCheck packedFactorsEven (row0451.map Prod.fst) evenDots0451 641 10 = true := by
  decide +kernel

theorem oddSum0451_checked :
    packedSumCheck packedFactorsOdd (row0451.map Prod.snd) oddDots0451 641 10 = true := by
  decide +kernel

theorem evenSum0452_checked :
    packedSumCheck packedFactorsEven (row0452.map Prod.fst) evenDots0452 641 10 = true := by
  decide +kernel

theorem oddSum0452_checked :
    packedSumCheck packedFactorsOdd (row0452.map Prod.snd) oddDots0452 641 10 = true := by
  decide +kernel

theorem evenSum0453_checked :
    packedSumCheck packedFactorsEven (row0453.map Prod.fst) evenDots0453 641 10 = true := by
  decide +kernel

theorem oddSum0453_checked :
    packedSumCheck packedFactorsOdd (row0453.map Prod.snd) oddDots0453 641 10 = true := by
  decide +kernel

theorem evenSum0454_checked :
    packedSumCheck packedFactorsEven (row0454.map Prod.fst) evenDots0454 641 10 = true := by
  decide +kernel

theorem oddSum0454_checked :
    packedSumCheck packedFactorsOdd (row0454.map Prod.snd) oddDots0454 641 10 = true := by
  decide +kernel

theorem evenSum0455_checked :
    packedSumCheck packedFactorsEven (row0455.map Prod.fst) evenDots0455 641 10 = true := by
  decide +kernel

theorem oddSum0455_checked :
    packedSumCheck packedFactorsOdd (row0455.map Prod.snd) oddDots0455 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
