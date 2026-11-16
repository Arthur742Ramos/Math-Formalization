module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows065
public import ErdosOverlap.Certificate.Native6Grid.PackedDots065

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0520_checked :
    packedSumCheck packedFactorsEven (row0520.map Prod.fst) evenDots0520 641 10 = true := by
  decide +kernel

theorem oddSum0520_checked :
    packedSumCheck packedFactorsOdd (row0520.map Prod.snd) oddDots0520 641 10 = true := by
  decide +kernel

theorem evenSum0521_checked :
    packedSumCheck packedFactorsEven (row0521.map Prod.fst) evenDots0521 641 10 = true := by
  decide +kernel

theorem oddSum0521_checked :
    packedSumCheck packedFactorsOdd (row0521.map Prod.snd) oddDots0521 641 10 = true := by
  decide +kernel

theorem evenSum0522_checked :
    packedSumCheck packedFactorsEven (row0522.map Prod.fst) evenDots0522 641 10 = true := by
  decide +kernel

theorem oddSum0522_checked :
    packedSumCheck packedFactorsOdd (row0522.map Prod.snd) oddDots0522 641 10 = true := by
  decide +kernel

theorem evenSum0523_checked :
    packedSumCheck packedFactorsEven (row0523.map Prod.fst) evenDots0523 641 10 = true := by
  decide +kernel

theorem oddSum0523_checked :
    packedSumCheck packedFactorsOdd (row0523.map Prod.snd) oddDots0523 641 10 = true := by
  decide +kernel

theorem evenSum0524_checked :
    packedSumCheck packedFactorsEven (row0524.map Prod.fst) evenDots0524 641 10 = true := by
  decide +kernel

theorem oddSum0524_checked :
    packedSumCheck packedFactorsOdd (row0524.map Prod.snd) oddDots0524 641 10 = true := by
  decide +kernel

theorem evenSum0525_checked :
    packedSumCheck packedFactorsEven (row0525.map Prod.fst) evenDots0525 641 10 = true := by
  decide +kernel

theorem oddSum0525_checked :
    packedSumCheck packedFactorsOdd (row0525.map Prod.snd) oddDots0525 641 10 = true := by
  decide +kernel

theorem evenSum0526_checked :
    packedSumCheck packedFactorsEven (row0526.map Prod.fst) evenDots0526 641 10 = true := by
  decide +kernel

theorem oddSum0526_checked :
    packedSumCheck packedFactorsOdd (row0526.map Prod.snd) oddDots0526 641 10 = true := by
  decide +kernel

theorem evenSum0527_checked :
    packedSumCheck packedFactorsEven (row0527.map Prod.fst) evenDots0527 641 10 = true := by
  decide +kernel

theorem oddSum0527_checked :
    packedSumCheck packedFactorsOdd (row0527.map Prod.snd) oddDots0527 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
