module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows045
public import ErdosOverlap.Certificate.Native6Grid.PackedDots045

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0360_checked :
    packedSumCheck packedFactorsEven (row0360.map Prod.fst) evenDots0360 641 10 = true := by
  decide +kernel

theorem oddSum0360_checked :
    packedSumCheck packedFactorsOdd (row0360.map Prod.snd) oddDots0360 641 10 = true := by
  decide +kernel

theorem evenSum0361_checked :
    packedSumCheck packedFactorsEven (row0361.map Prod.fst) evenDots0361 641 10 = true := by
  decide +kernel

theorem oddSum0361_checked :
    packedSumCheck packedFactorsOdd (row0361.map Prod.snd) oddDots0361 641 10 = true := by
  decide +kernel

theorem evenSum0362_checked :
    packedSumCheck packedFactorsEven (row0362.map Prod.fst) evenDots0362 641 10 = true := by
  decide +kernel

theorem oddSum0362_checked :
    packedSumCheck packedFactorsOdd (row0362.map Prod.snd) oddDots0362 641 10 = true := by
  decide +kernel

theorem evenSum0363_checked :
    packedSumCheck packedFactorsEven (row0363.map Prod.fst) evenDots0363 641 10 = true := by
  decide +kernel

theorem oddSum0363_checked :
    packedSumCheck packedFactorsOdd (row0363.map Prod.snd) oddDots0363 641 10 = true := by
  decide +kernel

theorem evenSum0364_checked :
    packedSumCheck packedFactorsEven (row0364.map Prod.fst) evenDots0364 641 10 = true := by
  decide +kernel

theorem oddSum0364_checked :
    packedSumCheck packedFactorsOdd (row0364.map Prod.snd) oddDots0364 641 10 = true := by
  decide +kernel

theorem evenSum0365_checked :
    packedSumCheck packedFactorsEven (row0365.map Prod.fst) evenDots0365 641 10 = true := by
  decide +kernel

theorem oddSum0365_checked :
    packedSumCheck packedFactorsOdd (row0365.map Prod.snd) oddDots0365 641 10 = true := by
  decide +kernel

theorem evenSum0366_checked :
    packedSumCheck packedFactorsEven (row0366.map Prod.fst) evenDots0366 641 10 = true := by
  decide +kernel

theorem oddSum0366_checked :
    packedSumCheck packedFactorsOdd (row0366.map Prod.snd) oddDots0366 641 10 = true := by
  decide +kernel

theorem evenSum0367_checked :
    packedSumCheck packedFactorsEven (row0367.map Prod.fst) evenDots0367 641 10 = true := by
  decide +kernel

theorem oddSum0367_checked :
    packedSumCheck packedFactorsOdd (row0367.map Prod.snd) oddDots0367 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
