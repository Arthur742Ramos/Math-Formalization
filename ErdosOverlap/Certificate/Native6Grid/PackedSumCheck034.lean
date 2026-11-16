module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows034
public import ErdosOverlap.Certificate.Native6Grid.PackedDots034

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0272_checked :
    packedSumCheck packedFactorsEven (row0272.map Prod.fst) evenDots0272 641 10 = true := by
  decide +kernel

theorem oddSum0272_checked :
    packedSumCheck packedFactorsOdd (row0272.map Prod.snd) oddDots0272 641 10 = true := by
  decide +kernel

theorem evenSum0273_checked :
    packedSumCheck packedFactorsEven (row0273.map Prod.fst) evenDots0273 641 10 = true := by
  decide +kernel

theorem oddSum0273_checked :
    packedSumCheck packedFactorsOdd (row0273.map Prod.snd) oddDots0273 641 10 = true := by
  decide +kernel

theorem evenSum0274_checked :
    packedSumCheck packedFactorsEven (row0274.map Prod.fst) evenDots0274 641 10 = true := by
  decide +kernel

theorem oddSum0274_checked :
    packedSumCheck packedFactorsOdd (row0274.map Prod.snd) oddDots0274 641 10 = true := by
  decide +kernel

theorem evenSum0275_checked :
    packedSumCheck packedFactorsEven (row0275.map Prod.fst) evenDots0275 641 10 = true := by
  decide +kernel

theorem oddSum0275_checked :
    packedSumCheck packedFactorsOdd (row0275.map Prod.snd) oddDots0275 641 10 = true := by
  decide +kernel

theorem evenSum0276_checked :
    packedSumCheck packedFactorsEven (row0276.map Prod.fst) evenDots0276 641 10 = true := by
  decide +kernel

theorem oddSum0276_checked :
    packedSumCheck packedFactorsOdd (row0276.map Prod.snd) oddDots0276 641 10 = true := by
  decide +kernel

theorem evenSum0277_checked :
    packedSumCheck packedFactorsEven (row0277.map Prod.fst) evenDots0277 641 10 = true := by
  decide +kernel

theorem oddSum0277_checked :
    packedSumCheck packedFactorsOdd (row0277.map Prod.snd) oddDots0277 641 10 = true := by
  decide +kernel

theorem evenSum0278_checked :
    packedSumCheck packedFactorsEven (row0278.map Prod.fst) evenDots0278 641 10 = true := by
  decide +kernel

theorem oddSum0278_checked :
    packedSumCheck packedFactorsOdd (row0278.map Prod.snd) oddDots0278 641 10 = true := by
  decide +kernel

theorem evenSum0279_checked :
    packedSumCheck packedFactorsEven (row0279.map Prod.fst) evenDots0279 641 10 = true := by
  decide +kernel

theorem oddSum0279_checked :
    packedSumCheck packedFactorsOdd (row0279.map Prod.snd) oddDots0279 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
