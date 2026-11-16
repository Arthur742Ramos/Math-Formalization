module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows083
public import ErdosOverlap.Certificate.Native6Grid.PackedDots083

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0664_checked :
    packedSumCheck packedFactorsEven (row0664.map Prod.fst) evenDots0664 641 10 = true := by
  decide +kernel

theorem oddSum0664_checked :
    packedSumCheck packedFactorsOdd (row0664.map Prod.snd) oddDots0664 641 10 = true := by
  decide +kernel

theorem evenSum0665_checked :
    packedSumCheck packedFactorsEven (row0665.map Prod.fst) evenDots0665 641 10 = true := by
  decide +kernel

theorem oddSum0665_checked :
    packedSumCheck packedFactorsOdd (row0665.map Prod.snd) oddDots0665 641 10 = true := by
  decide +kernel

theorem evenSum0666_checked :
    packedSumCheck packedFactorsEven (row0666.map Prod.fst) evenDots0666 641 10 = true := by
  decide +kernel

theorem oddSum0666_checked :
    packedSumCheck packedFactorsOdd (row0666.map Prod.snd) oddDots0666 641 10 = true := by
  decide +kernel

theorem evenSum0667_checked :
    packedSumCheck packedFactorsEven (row0667.map Prod.fst) evenDots0667 641 10 = true := by
  decide +kernel

theorem oddSum0667_checked :
    packedSumCheck packedFactorsOdd (row0667.map Prod.snd) oddDots0667 641 10 = true := by
  decide +kernel

theorem evenSum0668_checked :
    packedSumCheck packedFactorsEven (row0668.map Prod.fst) evenDots0668 641 10 = true := by
  decide +kernel

theorem oddSum0668_checked :
    packedSumCheck packedFactorsOdd (row0668.map Prod.snd) oddDots0668 641 10 = true := by
  decide +kernel

theorem evenSum0669_checked :
    packedSumCheck packedFactorsEven (row0669.map Prod.fst) evenDots0669 641 10 = true := by
  decide +kernel

theorem oddSum0669_checked :
    packedSumCheck packedFactorsOdd (row0669.map Prod.snd) oddDots0669 641 10 = true := by
  decide +kernel

theorem evenSum0670_checked :
    packedSumCheck packedFactorsEven (row0670.map Prod.fst) evenDots0670 641 10 = true := by
  decide +kernel

theorem oddSum0670_checked :
    packedSumCheck packedFactorsOdd (row0670.map Prod.snd) oddDots0670 641 10 = true := by
  decide +kernel

theorem evenSum0671_checked :
    packedSumCheck packedFactorsEven (row0671.map Prod.fst) evenDots0671 641 10 = true := by
  decide +kernel

theorem oddSum0671_checked :
    packedSumCheck packedFactorsOdd (row0671.map Prod.snd) oddDots0671 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
