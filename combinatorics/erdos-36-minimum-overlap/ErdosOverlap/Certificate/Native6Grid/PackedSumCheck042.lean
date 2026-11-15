module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows042
public import ErdosOverlap.Certificate.Native6Grid.PackedDots042

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0336_checked :
    packedSumCheck packedFactorsEven (row0336.map Prod.fst) evenDots0336 641 10 = true := by
  decide +kernel

theorem oddSum0336_checked :
    packedSumCheck packedFactorsOdd (row0336.map Prod.snd) oddDots0336 641 10 = true := by
  decide +kernel

theorem evenSum0337_checked :
    packedSumCheck packedFactorsEven (row0337.map Prod.fst) evenDots0337 641 10 = true := by
  decide +kernel

theorem oddSum0337_checked :
    packedSumCheck packedFactorsOdd (row0337.map Prod.snd) oddDots0337 641 10 = true := by
  decide +kernel

theorem evenSum0338_checked :
    packedSumCheck packedFactorsEven (row0338.map Prod.fst) evenDots0338 641 10 = true := by
  decide +kernel

theorem oddSum0338_checked :
    packedSumCheck packedFactorsOdd (row0338.map Prod.snd) oddDots0338 641 10 = true := by
  decide +kernel

theorem evenSum0339_checked :
    packedSumCheck packedFactorsEven (row0339.map Prod.fst) evenDots0339 641 10 = true := by
  decide +kernel

theorem oddSum0339_checked :
    packedSumCheck packedFactorsOdd (row0339.map Prod.snd) oddDots0339 641 10 = true := by
  decide +kernel

theorem evenSum0340_checked :
    packedSumCheck packedFactorsEven (row0340.map Prod.fst) evenDots0340 641 10 = true := by
  decide +kernel

theorem oddSum0340_checked :
    packedSumCheck packedFactorsOdd (row0340.map Prod.snd) oddDots0340 641 10 = true := by
  decide +kernel

theorem evenSum0341_checked :
    packedSumCheck packedFactorsEven (row0341.map Prod.fst) evenDots0341 641 10 = true := by
  decide +kernel

theorem oddSum0341_checked :
    packedSumCheck packedFactorsOdd (row0341.map Prod.snd) oddDots0341 641 10 = true := by
  decide +kernel

theorem evenSum0342_checked :
    packedSumCheck packedFactorsEven (row0342.map Prod.fst) evenDots0342 641 10 = true := by
  decide +kernel

theorem oddSum0342_checked :
    packedSumCheck packedFactorsOdd (row0342.map Prod.snd) oddDots0342 641 10 = true := by
  decide +kernel

theorem evenSum0343_checked :
    packedSumCheck packedFactorsEven (row0343.map Prod.fst) evenDots0343 641 10 = true := by
  decide +kernel

theorem oddSum0343_checked :
    packedSumCheck packedFactorsOdd (row0343.map Prod.snd) oddDots0343 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
