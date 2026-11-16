module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows085
public import ErdosOverlap.Certificate.Native6Grid.PackedDots085

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0680_checked :
    packedSumCheck packedFactorsEven (row0680.map Prod.fst) evenDots0680 641 10 = true := by
  decide +kernel

theorem oddSum0680_checked :
    packedSumCheck packedFactorsOdd (row0680.map Prod.snd) oddDots0680 641 10 = true := by
  decide +kernel

theorem evenSum0681_checked :
    packedSumCheck packedFactorsEven (row0681.map Prod.fst) evenDots0681 641 10 = true := by
  decide +kernel

theorem oddSum0681_checked :
    packedSumCheck packedFactorsOdd (row0681.map Prod.snd) oddDots0681 641 10 = true := by
  decide +kernel

theorem evenSum0682_checked :
    packedSumCheck packedFactorsEven (row0682.map Prod.fst) evenDots0682 641 10 = true := by
  decide +kernel

theorem oddSum0682_checked :
    packedSumCheck packedFactorsOdd (row0682.map Prod.snd) oddDots0682 641 10 = true := by
  decide +kernel

theorem evenSum0683_checked :
    packedSumCheck packedFactorsEven (row0683.map Prod.fst) evenDots0683 641 10 = true := by
  decide +kernel

theorem oddSum0683_checked :
    packedSumCheck packedFactorsOdd (row0683.map Prod.snd) oddDots0683 641 10 = true := by
  decide +kernel

theorem evenSum0684_checked :
    packedSumCheck packedFactorsEven (row0684.map Prod.fst) evenDots0684 641 10 = true := by
  decide +kernel

theorem oddSum0684_checked :
    packedSumCheck packedFactorsOdd (row0684.map Prod.snd) oddDots0684 641 10 = true := by
  decide +kernel

theorem evenSum0685_checked :
    packedSumCheck packedFactorsEven (row0685.map Prod.fst) evenDots0685 641 10 = true := by
  decide +kernel

theorem oddSum0685_checked :
    packedSumCheck packedFactorsOdd (row0685.map Prod.snd) oddDots0685 641 10 = true := by
  decide +kernel

theorem evenSum0686_checked :
    packedSumCheck packedFactorsEven (row0686.map Prod.fst) evenDots0686 641 10 = true := by
  decide +kernel

theorem oddSum0686_checked :
    packedSumCheck packedFactorsOdd (row0686.map Prod.snd) oddDots0686 641 10 = true := by
  decide +kernel

theorem evenSum0687_checked :
    packedSumCheck packedFactorsEven (row0687.map Prod.fst) evenDots0687 641 10 = true := by
  decide +kernel

theorem oddSum0687_checked :
    packedSumCheck packedFactorsOdd (row0687.map Prod.snd) oddDots0687 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
