module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows038
public import ErdosOverlap.Certificate.Native6Grid.PackedDots038

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0304_checked :
    packedSumCheck packedFactorsEven (row0304.map Prod.fst) evenDots0304 641 10 = true := by
  decide +kernel

theorem oddSum0304_checked :
    packedSumCheck packedFactorsOdd (row0304.map Prod.snd) oddDots0304 641 10 = true := by
  decide +kernel

theorem evenSum0305_checked :
    packedSumCheck packedFactorsEven (row0305.map Prod.fst) evenDots0305 641 10 = true := by
  decide +kernel

theorem oddSum0305_checked :
    packedSumCheck packedFactorsOdd (row0305.map Prod.snd) oddDots0305 641 10 = true := by
  decide +kernel

theorem evenSum0306_checked :
    packedSumCheck packedFactorsEven (row0306.map Prod.fst) evenDots0306 641 10 = true := by
  decide +kernel

theorem oddSum0306_checked :
    packedSumCheck packedFactorsOdd (row0306.map Prod.snd) oddDots0306 641 10 = true := by
  decide +kernel

theorem evenSum0307_checked :
    packedSumCheck packedFactorsEven (row0307.map Prod.fst) evenDots0307 641 10 = true := by
  decide +kernel

theorem oddSum0307_checked :
    packedSumCheck packedFactorsOdd (row0307.map Prod.snd) oddDots0307 641 10 = true := by
  decide +kernel

theorem evenSum0308_checked :
    packedSumCheck packedFactorsEven (row0308.map Prod.fst) evenDots0308 641 10 = true := by
  decide +kernel

theorem oddSum0308_checked :
    packedSumCheck packedFactorsOdd (row0308.map Prod.snd) oddDots0308 641 10 = true := by
  decide +kernel

theorem evenSum0309_checked :
    packedSumCheck packedFactorsEven (row0309.map Prod.fst) evenDots0309 641 10 = true := by
  decide +kernel

theorem oddSum0309_checked :
    packedSumCheck packedFactorsOdd (row0309.map Prod.snd) oddDots0309 641 10 = true := by
  decide +kernel

theorem evenSum0310_checked :
    packedSumCheck packedFactorsEven (row0310.map Prod.fst) evenDots0310 641 10 = true := by
  decide +kernel

theorem oddSum0310_checked :
    packedSumCheck packedFactorsOdd (row0310.map Prod.snd) oddDots0310 641 10 = true := by
  decide +kernel

theorem evenSum0311_checked :
    packedSumCheck packedFactorsEven (row0311.map Prod.fst) evenDots0311 641 10 = true := by
  decide +kernel

theorem oddSum0311_checked :
    packedSumCheck packedFactorsOdd (row0311.map Prod.snd) oddDots0311 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
