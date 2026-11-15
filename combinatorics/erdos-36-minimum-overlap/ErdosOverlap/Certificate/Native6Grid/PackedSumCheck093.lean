module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows093
public import ErdosOverlap.Certificate.Native6Grid.PackedDots093

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0744_checked :
    packedSumCheck packedFactorsEven (row0744.map Prod.fst) evenDots0744 641 10 = true := by
  decide +kernel

theorem oddSum0744_checked :
    packedSumCheck packedFactorsOdd (row0744.map Prod.snd) oddDots0744 641 10 = true := by
  decide +kernel

theorem evenSum0745_checked :
    packedSumCheck packedFactorsEven (row0745.map Prod.fst) evenDots0745 641 10 = true := by
  decide +kernel

theorem oddSum0745_checked :
    packedSumCheck packedFactorsOdd (row0745.map Prod.snd) oddDots0745 641 10 = true := by
  decide +kernel

theorem evenSum0746_checked :
    packedSumCheck packedFactorsEven (row0746.map Prod.fst) evenDots0746 641 10 = true := by
  decide +kernel

theorem oddSum0746_checked :
    packedSumCheck packedFactorsOdd (row0746.map Prod.snd) oddDots0746 641 10 = true := by
  decide +kernel

theorem evenSum0747_checked :
    packedSumCheck packedFactorsEven (row0747.map Prod.fst) evenDots0747 641 10 = true := by
  decide +kernel

theorem oddSum0747_checked :
    packedSumCheck packedFactorsOdd (row0747.map Prod.snd) oddDots0747 641 10 = true := by
  decide +kernel

theorem evenSum0748_checked :
    packedSumCheck packedFactorsEven (row0748.map Prod.fst) evenDots0748 641 10 = true := by
  decide +kernel

theorem oddSum0748_checked :
    packedSumCheck packedFactorsOdd (row0748.map Prod.snd) oddDots0748 641 10 = true := by
  decide +kernel

theorem evenSum0749_checked :
    packedSumCheck packedFactorsEven (row0749.map Prod.fst) evenDots0749 641 10 = true := by
  decide +kernel

theorem oddSum0749_checked :
    packedSumCheck packedFactorsOdd (row0749.map Prod.snd) oddDots0749 641 10 = true := by
  decide +kernel

theorem evenSum0750_checked :
    packedSumCheck packedFactorsEven (row0750.map Prod.fst) evenDots0750 641 10 = true := by
  decide +kernel

theorem oddSum0750_checked :
    packedSumCheck packedFactorsOdd (row0750.map Prod.snd) oddDots0750 641 10 = true := by
  decide +kernel

theorem evenSum0751_checked :
    packedSumCheck packedFactorsEven (row0751.map Prod.fst) evenDots0751 641 10 = true := by
  decide +kernel

theorem oddSum0751_checked :
    packedSumCheck packedFactorsOdd (row0751.map Prod.snd) oddDots0751 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
