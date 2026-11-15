module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows060
public import ErdosOverlap.Certificate.Native6Grid.PackedDots060

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0480_checked :
    packedSumCheck packedFactorsEven (row0480.map Prod.fst) evenDots0480 641 10 = true := by
  decide +kernel

theorem oddSum0480_checked :
    packedSumCheck packedFactorsOdd (row0480.map Prod.snd) oddDots0480 641 10 = true := by
  decide +kernel

theorem evenSum0481_checked :
    packedSumCheck packedFactorsEven (row0481.map Prod.fst) evenDots0481 641 10 = true := by
  decide +kernel

theorem oddSum0481_checked :
    packedSumCheck packedFactorsOdd (row0481.map Prod.snd) oddDots0481 641 10 = true := by
  decide +kernel

theorem evenSum0482_checked :
    packedSumCheck packedFactorsEven (row0482.map Prod.fst) evenDots0482 641 10 = true := by
  decide +kernel

theorem oddSum0482_checked :
    packedSumCheck packedFactorsOdd (row0482.map Prod.snd) oddDots0482 641 10 = true := by
  decide +kernel

theorem evenSum0483_checked :
    packedSumCheck packedFactorsEven (row0483.map Prod.fst) evenDots0483 641 10 = true := by
  decide +kernel

theorem oddSum0483_checked :
    packedSumCheck packedFactorsOdd (row0483.map Prod.snd) oddDots0483 641 10 = true := by
  decide +kernel

theorem evenSum0484_checked :
    packedSumCheck packedFactorsEven (row0484.map Prod.fst) evenDots0484 641 10 = true := by
  decide +kernel

theorem oddSum0484_checked :
    packedSumCheck packedFactorsOdd (row0484.map Prod.snd) oddDots0484 641 10 = true := by
  decide +kernel

theorem evenSum0485_checked :
    packedSumCheck packedFactorsEven (row0485.map Prod.fst) evenDots0485 641 10 = true := by
  decide +kernel

theorem oddSum0485_checked :
    packedSumCheck packedFactorsOdd (row0485.map Prod.snd) oddDots0485 641 10 = true := by
  decide +kernel

theorem evenSum0486_checked :
    packedSumCheck packedFactorsEven (row0486.map Prod.fst) evenDots0486 641 10 = true := by
  decide +kernel

theorem oddSum0486_checked :
    packedSumCheck packedFactorsOdd (row0486.map Prod.snd) oddDots0486 641 10 = true := by
  decide +kernel

theorem evenSum0487_checked :
    packedSumCheck packedFactorsEven (row0487.map Prod.fst) evenDots0487 641 10 = true := by
  decide +kernel

theorem oddSum0487_checked :
    packedSumCheck packedFactorsOdd (row0487.map Prod.snd) oddDots0487 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
