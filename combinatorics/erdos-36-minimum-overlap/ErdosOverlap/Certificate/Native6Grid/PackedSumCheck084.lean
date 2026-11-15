module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows084
public import ErdosOverlap.Certificate.Native6Grid.PackedDots084

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0672_checked :
    packedSumCheck packedFactorsEven (row0672.map Prod.fst) evenDots0672 641 10 = true := by
  decide +kernel

theorem oddSum0672_checked :
    packedSumCheck packedFactorsOdd (row0672.map Prod.snd) oddDots0672 641 10 = true := by
  decide +kernel

theorem evenSum0673_checked :
    packedSumCheck packedFactorsEven (row0673.map Prod.fst) evenDots0673 641 10 = true := by
  decide +kernel

theorem oddSum0673_checked :
    packedSumCheck packedFactorsOdd (row0673.map Prod.snd) oddDots0673 641 10 = true := by
  decide +kernel

theorem evenSum0674_checked :
    packedSumCheck packedFactorsEven (row0674.map Prod.fst) evenDots0674 641 10 = true := by
  decide +kernel

theorem oddSum0674_checked :
    packedSumCheck packedFactorsOdd (row0674.map Prod.snd) oddDots0674 641 10 = true := by
  decide +kernel

theorem evenSum0675_checked :
    packedSumCheck packedFactorsEven (row0675.map Prod.fst) evenDots0675 641 10 = true := by
  decide +kernel

theorem oddSum0675_checked :
    packedSumCheck packedFactorsOdd (row0675.map Prod.snd) oddDots0675 641 10 = true := by
  decide +kernel

theorem evenSum0676_checked :
    packedSumCheck packedFactorsEven (row0676.map Prod.fst) evenDots0676 641 10 = true := by
  decide +kernel

theorem oddSum0676_checked :
    packedSumCheck packedFactorsOdd (row0676.map Prod.snd) oddDots0676 641 10 = true := by
  decide +kernel

theorem evenSum0677_checked :
    packedSumCheck packedFactorsEven (row0677.map Prod.fst) evenDots0677 641 10 = true := by
  decide +kernel

theorem oddSum0677_checked :
    packedSumCheck packedFactorsOdd (row0677.map Prod.snd) oddDots0677 641 10 = true := by
  decide +kernel

theorem evenSum0678_checked :
    packedSumCheck packedFactorsEven (row0678.map Prod.fst) evenDots0678 641 10 = true := by
  decide +kernel

theorem oddSum0678_checked :
    packedSumCheck packedFactorsOdd (row0678.map Prod.snd) oddDots0678 641 10 = true := by
  decide +kernel

theorem evenSum0679_checked :
    packedSumCheck packedFactorsEven (row0679.map Prod.fst) evenDots0679 641 10 = true := by
  decide +kernel

theorem oddSum0679_checked :
    packedSumCheck packedFactorsOdd (row0679.map Prod.snd) oddDots0679 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
