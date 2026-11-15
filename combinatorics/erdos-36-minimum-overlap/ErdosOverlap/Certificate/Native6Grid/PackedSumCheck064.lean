module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows064
public import ErdosOverlap.Certificate.Native6Grid.PackedDots064

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0512_checked :
    packedSumCheck packedFactorsEven (row0512.map Prod.fst) evenDots0512 641 10 = true := by
  decide +kernel

theorem oddSum0512_checked :
    packedSumCheck packedFactorsOdd (row0512.map Prod.snd) oddDots0512 641 10 = true := by
  decide +kernel

theorem evenSum0513_checked :
    packedSumCheck packedFactorsEven (row0513.map Prod.fst) evenDots0513 641 10 = true := by
  decide +kernel

theorem oddSum0513_checked :
    packedSumCheck packedFactorsOdd (row0513.map Prod.snd) oddDots0513 641 10 = true := by
  decide +kernel

theorem evenSum0514_checked :
    packedSumCheck packedFactorsEven (row0514.map Prod.fst) evenDots0514 641 10 = true := by
  decide +kernel

theorem oddSum0514_checked :
    packedSumCheck packedFactorsOdd (row0514.map Prod.snd) oddDots0514 641 10 = true := by
  decide +kernel

theorem evenSum0515_checked :
    packedSumCheck packedFactorsEven (row0515.map Prod.fst) evenDots0515 641 10 = true := by
  decide +kernel

theorem oddSum0515_checked :
    packedSumCheck packedFactorsOdd (row0515.map Prod.snd) oddDots0515 641 10 = true := by
  decide +kernel

theorem evenSum0516_checked :
    packedSumCheck packedFactorsEven (row0516.map Prod.fst) evenDots0516 641 10 = true := by
  decide +kernel

theorem oddSum0516_checked :
    packedSumCheck packedFactorsOdd (row0516.map Prod.snd) oddDots0516 641 10 = true := by
  decide +kernel

theorem evenSum0517_checked :
    packedSumCheck packedFactorsEven (row0517.map Prod.fst) evenDots0517 641 10 = true := by
  decide +kernel

theorem oddSum0517_checked :
    packedSumCheck packedFactorsOdd (row0517.map Prod.snd) oddDots0517 641 10 = true := by
  decide +kernel

theorem evenSum0518_checked :
    packedSumCheck packedFactorsEven (row0518.map Prod.fst) evenDots0518 641 10 = true := by
  decide +kernel

theorem oddSum0518_checked :
    packedSumCheck packedFactorsOdd (row0518.map Prod.snd) oddDots0518 641 10 = true := by
  decide +kernel

theorem evenSum0519_checked :
    packedSumCheck packedFactorsEven (row0519.map Prod.fst) evenDots0519 641 10 = true := by
  decide +kernel

theorem oddSum0519_checked :
    packedSumCheck packedFactorsOdd (row0519.map Prod.snd) oddDots0519 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
