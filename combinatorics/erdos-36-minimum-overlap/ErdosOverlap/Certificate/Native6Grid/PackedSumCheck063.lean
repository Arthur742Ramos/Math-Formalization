module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows063
public import ErdosOverlap.Certificate.Native6Grid.PackedDots063

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0504_checked :
    packedSumCheck packedFactorsEven (row0504.map Prod.fst) evenDots0504 641 10 = true := by
  decide +kernel

theorem oddSum0504_checked :
    packedSumCheck packedFactorsOdd (row0504.map Prod.snd) oddDots0504 641 10 = true := by
  decide +kernel

theorem evenSum0505_checked :
    packedSumCheck packedFactorsEven (row0505.map Prod.fst) evenDots0505 641 10 = true := by
  decide +kernel

theorem oddSum0505_checked :
    packedSumCheck packedFactorsOdd (row0505.map Prod.snd) oddDots0505 641 10 = true := by
  decide +kernel

theorem evenSum0506_checked :
    packedSumCheck packedFactorsEven (row0506.map Prod.fst) evenDots0506 641 10 = true := by
  decide +kernel

theorem oddSum0506_checked :
    packedSumCheck packedFactorsOdd (row0506.map Prod.snd) oddDots0506 641 10 = true := by
  decide +kernel

theorem evenSum0507_checked :
    packedSumCheck packedFactorsEven (row0507.map Prod.fst) evenDots0507 641 10 = true := by
  decide +kernel

theorem oddSum0507_checked :
    packedSumCheck packedFactorsOdd (row0507.map Prod.snd) oddDots0507 641 10 = true := by
  decide +kernel

theorem evenSum0508_checked :
    packedSumCheck packedFactorsEven (row0508.map Prod.fst) evenDots0508 641 10 = true := by
  decide +kernel

theorem oddSum0508_checked :
    packedSumCheck packedFactorsOdd (row0508.map Prod.snd) oddDots0508 641 10 = true := by
  decide +kernel

theorem evenSum0509_checked :
    packedSumCheck packedFactorsEven (row0509.map Prod.fst) evenDots0509 641 10 = true := by
  decide +kernel

theorem oddSum0509_checked :
    packedSumCheck packedFactorsOdd (row0509.map Prod.snd) oddDots0509 641 10 = true := by
  decide +kernel

theorem evenSum0510_checked :
    packedSumCheck packedFactorsEven (row0510.map Prod.fst) evenDots0510 641 10 = true := by
  decide +kernel

theorem oddSum0510_checked :
    packedSumCheck packedFactorsOdd (row0510.map Prod.snd) oddDots0510 641 10 = true := by
  decide +kernel

theorem evenSum0511_checked :
    packedSumCheck packedFactorsEven (row0511.map Prod.fst) evenDots0511 641 10 = true := by
  decide +kernel

theorem oddSum0511_checked :
    packedSumCheck packedFactorsOdd (row0511.map Prod.snd) oddDots0511 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
