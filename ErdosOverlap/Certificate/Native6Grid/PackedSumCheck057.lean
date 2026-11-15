module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows057
public import ErdosOverlap.Certificate.Native6Grid.PackedDots057

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0456_checked :
    packedSumCheck packedFactorsEven (row0456.map Prod.fst) evenDots0456 641 10 = true := by
  decide +kernel

theorem oddSum0456_checked :
    packedSumCheck packedFactorsOdd (row0456.map Prod.snd) oddDots0456 641 10 = true := by
  decide +kernel

theorem evenSum0457_checked :
    packedSumCheck packedFactorsEven (row0457.map Prod.fst) evenDots0457 641 10 = true := by
  decide +kernel

theorem oddSum0457_checked :
    packedSumCheck packedFactorsOdd (row0457.map Prod.snd) oddDots0457 641 10 = true := by
  decide +kernel

theorem evenSum0458_checked :
    packedSumCheck packedFactorsEven (row0458.map Prod.fst) evenDots0458 641 10 = true := by
  decide +kernel

theorem oddSum0458_checked :
    packedSumCheck packedFactorsOdd (row0458.map Prod.snd) oddDots0458 641 10 = true := by
  decide +kernel

theorem evenSum0459_checked :
    packedSumCheck packedFactorsEven (row0459.map Prod.fst) evenDots0459 641 10 = true := by
  decide +kernel

theorem oddSum0459_checked :
    packedSumCheck packedFactorsOdd (row0459.map Prod.snd) oddDots0459 641 10 = true := by
  decide +kernel

theorem evenSum0460_checked :
    packedSumCheck packedFactorsEven (row0460.map Prod.fst) evenDots0460 641 10 = true := by
  decide +kernel

theorem oddSum0460_checked :
    packedSumCheck packedFactorsOdd (row0460.map Prod.snd) oddDots0460 641 10 = true := by
  decide +kernel

theorem evenSum0461_checked :
    packedSumCheck packedFactorsEven (row0461.map Prod.fst) evenDots0461 641 10 = true := by
  decide +kernel

theorem oddSum0461_checked :
    packedSumCheck packedFactorsOdd (row0461.map Prod.snd) oddDots0461 641 10 = true := by
  decide +kernel

theorem evenSum0462_checked :
    packedSumCheck packedFactorsEven (row0462.map Prod.fst) evenDots0462 641 10 = true := by
  decide +kernel

theorem oddSum0462_checked :
    packedSumCheck packedFactorsOdd (row0462.map Prod.snd) oddDots0462 641 10 = true := by
  decide +kernel

theorem evenSum0463_checked :
    packedSumCheck packedFactorsEven (row0463.map Prod.fst) evenDots0463 641 10 = true := by
  decide +kernel

theorem oddSum0463_checked :
    packedSumCheck packedFactorsOdd (row0463.map Prod.snd) oddDots0463 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
