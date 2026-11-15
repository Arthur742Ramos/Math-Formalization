module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows061
public import ErdosOverlap.Certificate.Native6Grid.PackedDots061

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0488_checked :
    packedSumCheck packedFactorsEven (row0488.map Prod.fst) evenDots0488 641 10 = true := by
  decide +kernel

theorem oddSum0488_checked :
    packedSumCheck packedFactorsOdd (row0488.map Prod.snd) oddDots0488 641 10 = true := by
  decide +kernel

theorem evenSum0489_checked :
    packedSumCheck packedFactorsEven (row0489.map Prod.fst) evenDots0489 641 10 = true := by
  decide +kernel

theorem oddSum0489_checked :
    packedSumCheck packedFactorsOdd (row0489.map Prod.snd) oddDots0489 641 10 = true := by
  decide +kernel

theorem evenSum0490_checked :
    packedSumCheck packedFactorsEven (row0490.map Prod.fst) evenDots0490 641 10 = true := by
  decide +kernel

theorem oddSum0490_checked :
    packedSumCheck packedFactorsOdd (row0490.map Prod.snd) oddDots0490 641 10 = true := by
  decide +kernel

theorem evenSum0491_checked :
    packedSumCheck packedFactorsEven (row0491.map Prod.fst) evenDots0491 641 10 = true := by
  decide +kernel

theorem oddSum0491_checked :
    packedSumCheck packedFactorsOdd (row0491.map Prod.snd) oddDots0491 641 10 = true := by
  decide +kernel

theorem evenSum0492_checked :
    packedSumCheck packedFactorsEven (row0492.map Prod.fst) evenDots0492 641 10 = true := by
  decide +kernel

theorem oddSum0492_checked :
    packedSumCheck packedFactorsOdd (row0492.map Prod.snd) oddDots0492 641 10 = true := by
  decide +kernel

theorem evenSum0493_checked :
    packedSumCheck packedFactorsEven (row0493.map Prod.fst) evenDots0493 641 10 = true := by
  decide +kernel

theorem oddSum0493_checked :
    packedSumCheck packedFactorsOdd (row0493.map Prod.snd) oddDots0493 641 10 = true := by
  decide +kernel

theorem evenSum0494_checked :
    packedSumCheck packedFactorsEven (row0494.map Prod.fst) evenDots0494 641 10 = true := by
  decide +kernel

theorem oddSum0494_checked :
    packedSumCheck packedFactorsOdd (row0494.map Prod.snd) oddDots0494 641 10 = true := by
  decide +kernel

theorem evenSum0495_checked :
    packedSumCheck packedFactorsEven (row0495.map Prod.fst) evenDots0495 641 10 = true := by
  decide +kernel

theorem oddSum0495_checked :
    packedSumCheck packedFactorsOdd (row0495.map Prod.snd) oddDots0495 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
