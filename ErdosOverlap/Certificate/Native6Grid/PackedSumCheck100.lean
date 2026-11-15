module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows100
public import ErdosOverlap.Certificate.Native6Grid.PackedDots100

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0800_checked :
    packedSumCheck packedFactorsEven (row0800.map Prod.fst) evenDots0800 641 10 = true := by
  decide +kernel

theorem oddSum0800_checked :
    packedSumCheck packedFactorsOdd (row0800.map Prod.snd) oddDots0800 641 10 = true := by
  decide +kernel

theorem evenSum0801_checked :
    packedSumCheck packedFactorsEven (row0801.map Prod.fst) evenDots0801 641 10 = true := by
  decide +kernel

theorem oddSum0801_checked :
    packedSumCheck packedFactorsOdd (row0801.map Prod.snd) oddDots0801 641 10 = true := by
  decide +kernel

theorem evenSum0802_checked :
    packedSumCheck packedFactorsEven (row0802.map Prod.fst) evenDots0802 641 10 = true := by
  decide +kernel

theorem oddSum0802_checked :
    packedSumCheck packedFactorsOdd (row0802.map Prod.snd) oddDots0802 641 10 = true := by
  decide +kernel

theorem evenSum0803_checked :
    packedSumCheck packedFactorsEven (row0803.map Prod.fst) evenDots0803 641 10 = true := by
  decide +kernel

theorem oddSum0803_checked :
    packedSumCheck packedFactorsOdd (row0803.map Prod.snd) oddDots0803 641 10 = true := by
  decide +kernel

theorem evenSum0804_checked :
    packedSumCheck packedFactorsEven (row0804.map Prod.fst) evenDots0804 641 10 = true := by
  decide +kernel

theorem oddSum0804_checked :
    packedSumCheck packedFactorsOdd (row0804.map Prod.snd) oddDots0804 641 10 = true := by
  decide +kernel

theorem evenSum0805_checked :
    packedSumCheck packedFactorsEven (row0805.map Prod.fst) evenDots0805 641 10 = true := by
  decide +kernel

theorem oddSum0805_checked :
    packedSumCheck packedFactorsOdd (row0805.map Prod.snd) oddDots0805 641 10 = true := by
  decide +kernel

theorem evenSum0806_checked :
    packedSumCheck packedFactorsEven (row0806.map Prod.fst) evenDots0806 641 10 = true := by
  decide +kernel

theorem oddSum0806_checked :
    packedSumCheck packedFactorsOdd (row0806.map Prod.snd) oddDots0806 641 10 = true := by
  decide +kernel

theorem evenSum0807_checked :
    packedSumCheck packedFactorsEven (row0807.map Prod.fst) evenDots0807 641 10 = true := by
  decide +kernel

theorem oddSum0807_checked :
    packedSumCheck packedFactorsOdd (row0807.map Prod.snd) oddDots0807 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
