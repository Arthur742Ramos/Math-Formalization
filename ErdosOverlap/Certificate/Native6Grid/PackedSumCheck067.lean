module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows067
public import ErdosOverlap.Certificate.Native6Grid.PackedDots067

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0536_checked :
    packedSumCheck packedFactorsEven (row0536.map Prod.fst) evenDots0536 641 10 = true := by
  decide +kernel

theorem oddSum0536_checked :
    packedSumCheck packedFactorsOdd (row0536.map Prod.snd) oddDots0536 641 10 = true := by
  decide +kernel

theorem evenSum0537_checked :
    packedSumCheck packedFactorsEven (row0537.map Prod.fst) evenDots0537 641 10 = true := by
  decide +kernel

theorem oddSum0537_checked :
    packedSumCheck packedFactorsOdd (row0537.map Prod.snd) oddDots0537 641 10 = true := by
  decide +kernel

theorem evenSum0538_checked :
    packedSumCheck packedFactorsEven (row0538.map Prod.fst) evenDots0538 641 10 = true := by
  decide +kernel

theorem oddSum0538_checked :
    packedSumCheck packedFactorsOdd (row0538.map Prod.snd) oddDots0538 641 10 = true := by
  decide +kernel

theorem evenSum0539_checked :
    packedSumCheck packedFactorsEven (row0539.map Prod.fst) evenDots0539 641 10 = true := by
  decide +kernel

theorem oddSum0539_checked :
    packedSumCheck packedFactorsOdd (row0539.map Prod.snd) oddDots0539 641 10 = true := by
  decide +kernel

theorem evenSum0540_checked :
    packedSumCheck packedFactorsEven (row0540.map Prod.fst) evenDots0540 641 10 = true := by
  decide +kernel

theorem oddSum0540_checked :
    packedSumCheck packedFactorsOdd (row0540.map Prod.snd) oddDots0540 641 10 = true := by
  decide +kernel

theorem evenSum0541_checked :
    packedSumCheck packedFactorsEven (row0541.map Prod.fst) evenDots0541 641 10 = true := by
  decide +kernel

theorem oddSum0541_checked :
    packedSumCheck packedFactorsOdd (row0541.map Prod.snd) oddDots0541 641 10 = true := by
  decide +kernel

theorem evenSum0542_checked :
    packedSumCheck packedFactorsEven (row0542.map Prod.fst) evenDots0542 641 10 = true := by
  decide +kernel

theorem oddSum0542_checked :
    packedSumCheck packedFactorsOdd (row0542.map Prod.snd) oddDots0542 641 10 = true := by
  decide +kernel

theorem evenSum0543_checked :
    packedSumCheck packedFactorsEven (row0543.map Prod.fst) evenDots0543 641 10 = true := by
  decide +kernel

theorem oddSum0543_checked :
    packedSumCheck packedFactorsOdd (row0543.map Prod.snd) oddDots0543 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
