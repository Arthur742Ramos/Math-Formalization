module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows025
public import ErdosOverlap.Certificate.Native6Grid.PackedDots025

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0200_checked :
    packedSumCheck packedFactorsEven (row0200.map Prod.fst) evenDots0200 641 10 = true := by
  decide +kernel

theorem oddSum0200_checked :
    packedSumCheck packedFactorsOdd (row0200.map Prod.snd) oddDots0200 641 10 = true := by
  decide +kernel

theorem evenSum0201_checked :
    packedSumCheck packedFactorsEven (row0201.map Prod.fst) evenDots0201 641 10 = true := by
  decide +kernel

theorem oddSum0201_checked :
    packedSumCheck packedFactorsOdd (row0201.map Prod.snd) oddDots0201 641 10 = true := by
  decide +kernel

theorem evenSum0202_checked :
    packedSumCheck packedFactorsEven (row0202.map Prod.fst) evenDots0202 641 10 = true := by
  decide +kernel

theorem oddSum0202_checked :
    packedSumCheck packedFactorsOdd (row0202.map Prod.snd) oddDots0202 641 10 = true := by
  decide +kernel

theorem evenSum0203_checked :
    packedSumCheck packedFactorsEven (row0203.map Prod.fst) evenDots0203 641 10 = true := by
  decide +kernel

theorem oddSum0203_checked :
    packedSumCheck packedFactorsOdd (row0203.map Prod.snd) oddDots0203 641 10 = true := by
  decide +kernel

theorem evenSum0204_checked :
    packedSumCheck packedFactorsEven (row0204.map Prod.fst) evenDots0204 641 10 = true := by
  decide +kernel

theorem oddSum0204_checked :
    packedSumCheck packedFactorsOdd (row0204.map Prod.snd) oddDots0204 641 10 = true := by
  decide +kernel

theorem evenSum0205_checked :
    packedSumCheck packedFactorsEven (row0205.map Prod.fst) evenDots0205 641 10 = true := by
  decide +kernel

theorem oddSum0205_checked :
    packedSumCheck packedFactorsOdd (row0205.map Prod.snd) oddDots0205 641 10 = true := by
  decide +kernel

theorem evenSum0206_checked :
    packedSumCheck packedFactorsEven (row0206.map Prod.fst) evenDots0206 641 10 = true := by
  decide +kernel

theorem oddSum0206_checked :
    packedSumCheck packedFactorsOdd (row0206.map Prod.snd) oddDots0206 641 10 = true := by
  decide +kernel

theorem evenSum0207_checked :
    packedSumCheck packedFactorsEven (row0207.map Prod.fst) evenDots0207 641 10 = true := by
  decide +kernel

theorem oddSum0207_checked :
    packedSumCheck packedFactorsOdd (row0207.map Prod.snd) oddDots0207 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
