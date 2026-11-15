module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows014
public import ErdosOverlap.Certificate.Native6Grid.PackedDots014

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0112_checked :
    packedSumCheck packedFactorsEven (row0112.map Prod.fst) evenDots0112 641 10 = true := by
  decide +kernel

theorem oddSum0112_checked :
    packedSumCheck packedFactorsOdd (row0112.map Prod.snd) oddDots0112 641 10 = true := by
  decide +kernel

theorem evenSum0113_checked :
    packedSumCheck packedFactorsEven (row0113.map Prod.fst) evenDots0113 641 10 = true := by
  decide +kernel

theorem oddSum0113_checked :
    packedSumCheck packedFactorsOdd (row0113.map Prod.snd) oddDots0113 641 10 = true := by
  decide +kernel

theorem evenSum0114_checked :
    packedSumCheck packedFactorsEven (row0114.map Prod.fst) evenDots0114 641 10 = true := by
  decide +kernel

theorem oddSum0114_checked :
    packedSumCheck packedFactorsOdd (row0114.map Prod.snd) oddDots0114 641 10 = true := by
  decide +kernel

theorem evenSum0115_checked :
    packedSumCheck packedFactorsEven (row0115.map Prod.fst) evenDots0115 641 10 = true := by
  decide +kernel

theorem oddSum0115_checked :
    packedSumCheck packedFactorsOdd (row0115.map Prod.snd) oddDots0115 641 10 = true := by
  decide +kernel

theorem evenSum0116_checked :
    packedSumCheck packedFactorsEven (row0116.map Prod.fst) evenDots0116 641 10 = true := by
  decide +kernel

theorem oddSum0116_checked :
    packedSumCheck packedFactorsOdd (row0116.map Prod.snd) oddDots0116 641 10 = true := by
  decide +kernel

theorem evenSum0117_checked :
    packedSumCheck packedFactorsEven (row0117.map Prod.fst) evenDots0117 641 10 = true := by
  decide +kernel

theorem oddSum0117_checked :
    packedSumCheck packedFactorsOdd (row0117.map Prod.snd) oddDots0117 641 10 = true := by
  decide +kernel

theorem evenSum0118_checked :
    packedSumCheck packedFactorsEven (row0118.map Prod.fst) evenDots0118 641 10 = true := by
  decide +kernel

theorem oddSum0118_checked :
    packedSumCheck packedFactorsOdd (row0118.map Prod.snd) oddDots0118 641 10 = true := by
  decide +kernel

theorem evenSum0119_checked :
    packedSumCheck packedFactorsEven (row0119.map Prod.fst) evenDots0119 641 10 = true := by
  decide +kernel

theorem oddSum0119_checked :
    packedSumCheck packedFactorsOdd (row0119.map Prod.snd) oddDots0119 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
