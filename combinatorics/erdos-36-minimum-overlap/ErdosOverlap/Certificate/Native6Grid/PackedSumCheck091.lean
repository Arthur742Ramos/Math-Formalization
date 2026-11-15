module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows091
public import ErdosOverlap.Certificate.Native6Grid.PackedDots091

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0728_checked :
    packedSumCheck packedFactorsEven (row0728.map Prod.fst) evenDots0728 641 10 = true := by
  decide +kernel

theorem oddSum0728_checked :
    packedSumCheck packedFactorsOdd (row0728.map Prod.snd) oddDots0728 641 10 = true := by
  decide +kernel

theorem evenSum0729_checked :
    packedSumCheck packedFactorsEven (row0729.map Prod.fst) evenDots0729 641 10 = true := by
  decide +kernel

theorem oddSum0729_checked :
    packedSumCheck packedFactorsOdd (row0729.map Prod.snd) oddDots0729 641 10 = true := by
  decide +kernel

theorem evenSum0730_checked :
    packedSumCheck packedFactorsEven (row0730.map Prod.fst) evenDots0730 641 10 = true := by
  decide +kernel

theorem oddSum0730_checked :
    packedSumCheck packedFactorsOdd (row0730.map Prod.snd) oddDots0730 641 10 = true := by
  decide +kernel

theorem evenSum0731_checked :
    packedSumCheck packedFactorsEven (row0731.map Prod.fst) evenDots0731 641 10 = true := by
  decide +kernel

theorem oddSum0731_checked :
    packedSumCheck packedFactorsOdd (row0731.map Prod.snd) oddDots0731 641 10 = true := by
  decide +kernel

theorem evenSum0732_checked :
    packedSumCheck packedFactorsEven (row0732.map Prod.fst) evenDots0732 641 10 = true := by
  decide +kernel

theorem oddSum0732_checked :
    packedSumCheck packedFactorsOdd (row0732.map Prod.snd) oddDots0732 641 10 = true := by
  decide +kernel

theorem evenSum0733_checked :
    packedSumCheck packedFactorsEven (row0733.map Prod.fst) evenDots0733 641 10 = true := by
  decide +kernel

theorem oddSum0733_checked :
    packedSumCheck packedFactorsOdd (row0733.map Prod.snd) oddDots0733 641 10 = true := by
  decide +kernel

theorem evenSum0734_checked :
    packedSumCheck packedFactorsEven (row0734.map Prod.fst) evenDots0734 641 10 = true := by
  decide +kernel

theorem oddSum0734_checked :
    packedSumCheck packedFactorsOdd (row0734.map Prod.snd) oddDots0734 641 10 = true := by
  decide +kernel

theorem evenSum0735_checked :
    packedSumCheck packedFactorsEven (row0735.map Prod.fst) evenDots0735 641 10 = true := by
  decide +kernel

theorem oddSum0735_checked :
    packedSumCheck packedFactorsOdd (row0735.map Prod.snd) oddDots0735 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
