module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows082
public import ErdosOverlap.Certificate.Native6Grid.PackedDots082

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0656_checked :
    packedSumCheck packedFactorsEven (row0656.map Prod.fst) evenDots0656 641 10 = true := by
  decide +kernel

theorem oddSum0656_checked :
    packedSumCheck packedFactorsOdd (row0656.map Prod.snd) oddDots0656 641 10 = true := by
  decide +kernel

theorem evenSum0657_checked :
    packedSumCheck packedFactorsEven (row0657.map Prod.fst) evenDots0657 641 10 = true := by
  decide +kernel

theorem oddSum0657_checked :
    packedSumCheck packedFactorsOdd (row0657.map Prod.snd) oddDots0657 641 10 = true := by
  decide +kernel

theorem evenSum0658_checked :
    packedSumCheck packedFactorsEven (row0658.map Prod.fst) evenDots0658 641 10 = true := by
  decide +kernel

theorem oddSum0658_checked :
    packedSumCheck packedFactorsOdd (row0658.map Prod.snd) oddDots0658 641 10 = true := by
  decide +kernel

theorem evenSum0659_checked :
    packedSumCheck packedFactorsEven (row0659.map Prod.fst) evenDots0659 641 10 = true := by
  decide +kernel

theorem oddSum0659_checked :
    packedSumCheck packedFactorsOdd (row0659.map Prod.snd) oddDots0659 641 10 = true := by
  decide +kernel

theorem evenSum0660_checked :
    packedSumCheck packedFactorsEven (row0660.map Prod.fst) evenDots0660 641 10 = true := by
  decide +kernel

theorem oddSum0660_checked :
    packedSumCheck packedFactorsOdd (row0660.map Prod.snd) oddDots0660 641 10 = true := by
  decide +kernel

theorem evenSum0661_checked :
    packedSumCheck packedFactorsEven (row0661.map Prod.fst) evenDots0661 641 10 = true := by
  decide +kernel

theorem oddSum0661_checked :
    packedSumCheck packedFactorsOdd (row0661.map Prod.snd) oddDots0661 641 10 = true := by
  decide +kernel

theorem evenSum0662_checked :
    packedSumCheck packedFactorsEven (row0662.map Prod.fst) evenDots0662 641 10 = true := by
  decide +kernel

theorem oddSum0662_checked :
    packedSumCheck packedFactorsOdd (row0662.map Prod.snd) oddDots0662 641 10 = true := by
  decide +kernel

theorem evenSum0663_checked :
    packedSumCheck packedFactorsEven (row0663.map Prod.fst) evenDots0663 641 10 = true := by
  decide +kernel

theorem oddSum0663_checked :
    packedSumCheck packedFactorsOdd (row0663.map Prod.snd) oddDots0663 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
