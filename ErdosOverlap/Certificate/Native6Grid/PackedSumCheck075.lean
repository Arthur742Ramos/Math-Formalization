module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows075
public import ErdosOverlap.Certificate.Native6Grid.PackedDots075

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0600_checked :
    packedSumCheck packedFactorsEven (row0600.map Prod.fst) evenDots0600 641 10 = true := by
  decide +kernel

theorem oddSum0600_checked :
    packedSumCheck packedFactorsOdd (row0600.map Prod.snd) oddDots0600 641 10 = true := by
  decide +kernel

theorem evenSum0601_checked :
    packedSumCheck packedFactorsEven (row0601.map Prod.fst) evenDots0601 641 10 = true := by
  decide +kernel

theorem oddSum0601_checked :
    packedSumCheck packedFactorsOdd (row0601.map Prod.snd) oddDots0601 641 10 = true := by
  decide +kernel

theorem evenSum0602_checked :
    packedSumCheck packedFactorsEven (row0602.map Prod.fst) evenDots0602 641 10 = true := by
  decide +kernel

theorem oddSum0602_checked :
    packedSumCheck packedFactorsOdd (row0602.map Prod.snd) oddDots0602 641 10 = true := by
  decide +kernel

theorem evenSum0603_checked :
    packedSumCheck packedFactorsEven (row0603.map Prod.fst) evenDots0603 641 10 = true := by
  decide +kernel

theorem oddSum0603_checked :
    packedSumCheck packedFactorsOdd (row0603.map Prod.snd) oddDots0603 641 10 = true := by
  decide +kernel

theorem evenSum0604_checked :
    packedSumCheck packedFactorsEven (row0604.map Prod.fst) evenDots0604 641 10 = true := by
  decide +kernel

theorem oddSum0604_checked :
    packedSumCheck packedFactorsOdd (row0604.map Prod.snd) oddDots0604 641 10 = true := by
  decide +kernel

theorem evenSum0605_checked :
    packedSumCheck packedFactorsEven (row0605.map Prod.fst) evenDots0605 641 10 = true := by
  decide +kernel

theorem oddSum0605_checked :
    packedSumCheck packedFactorsOdd (row0605.map Prod.snd) oddDots0605 641 10 = true := by
  decide +kernel

theorem evenSum0606_checked :
    packedSumCheck packedFactorsEven (row0606.map Prod.fst) evenDots0606 641 10 = true := by
  decide +kernel

theorem oddSum0606_checked :
    packedSumCheck packedFactorsOdd (row0606.map Prod.snd) oddDots0606 641 10 = true := by
  decide +kernel

theorem evenSum0607_checked :
    packedSumCheck packedFactorsEven (row0607.map Prod.fst) evenDots0607 641 10 = true := by
  decide +kernel

theorem oddSum0607_checked :
    packedSumCheck packedFactorsOdd (row0607.map Prod.snd) oddDots0607 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
