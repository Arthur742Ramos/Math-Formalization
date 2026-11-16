module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows095
public import ErdosOverlap.Certificate.Native6Grid.PackedDots095

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0760_checked :
    packedSumCheck packedFactorsEven (row0760.map Prod.fst) evenDots0760 641 10 = true := by
  decide +kernel

theorem oddSum0760_checked :
    packedSumCheck packedFactorsOdd (row0760.map Prod.snd) oddDots0760 641 10 = true := by
  decide +kernel

theorem evenSum0761_checked :
    packedSumCheck packedFactorsEven (row0761.map Prod.fst) evenDots0761 641 10 = true := by
  decide +kernel

theorem oddSum0761_checked :
    packedSumCheck packedFactorsOdd (row0761.map Prod.snd) oddDots0761 641 10 = true := by
  decide +kernel

theorem evenSum0762_checked :
    packedSumCheck packedFactorsEven (row0762.map Prod.fst) evenDots0762 641 10 = true := by
  decide +kernel

theorem oddSum0762_checked :
    packedSumCheck packedFactorsOdd (row0762.map Prod.snd) oddDots0762 641 10 = true := by
  decide +kernel

theorem evenSum0763_checked :
    packedSumCheck packedFactorsEven (row0763.map Prod.fst) evenDots0763 641 10 = true := by
  decide +kernel

theorem oddSum0763_checked :
    packedSumCheck packedFactorsOdd (row0763.map Prod.snd) oddDots0763 641 10 = true := by
  decide +kernel

theorem evenSum0764_checked :
    packedSumCheck packedFactorsEven (row0764.map Prod.fst) evenDots0764 641 10 = true := by
  decide +kernel

theorem oddSum0764_checked :
    packedSumCheck packedFactorsOdd (row0764.map Prod.snd) oddDots0764 641 10 = true := by
  decide +kernel

theorem evenSum0765_checked :
    packedSumCheck packedFactorsEven (row0765.map Prod.fst) evenDots0765 641 10 = true := by
  decide +kernel

theorem oddSum0765_checked :
    packedSumCheck packedFactorsOdd (row0765.map Prod.snd) oddDots0765 641 10 = true := by
  decide +kernel

theorem evenSum0766_checked :
    packedSumCheck packedFactorsEven (row0766.map Prod.fst) evenDots0766 641 10 = true := by
  decide +kernel

theorem oddSum0766_checked :
    packedSumCheck packedFactorsOdd (row0766.map Prod.snd) oddDots0766 641 10 = true := by
  decide +kernel

theorem evenSum0767_checked :
    packedSumCheck packedFactorsEven (row0767.map Prod.fst) evenDots0767 641 10 = true := by
  decide +kernel

theorem oddSum0767_checked :
    packedSumCheck packedFactorsOdd (row0767.map Prod.snd) oddDots0767 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
