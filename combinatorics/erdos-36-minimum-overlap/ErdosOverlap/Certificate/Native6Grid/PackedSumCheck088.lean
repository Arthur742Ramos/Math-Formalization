module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows088
public import ErdosOverlap.Certificate.Native6Grid.PackedDots088

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0704_checked :
    packedSumCheck packedFactorsEven (row0704.map Prod.fst) evenDots0704 641 10 = true := by
  decide +kernel

theorem oddSum0704_checked :
    packedSumCheck packedFactorsOdd (row0704.map Prod.snd) oddDots0704 641 10 = true := by
  decide +kernel

theorem evenSum0705_checked :
    packedSumCheck packedFactorsEven (row0705.map Prod.fst) evenDots0705 641 10 = true := by
  decide +kernel

theorem oddSum0705_checked :
    packedSumCheck packedFactorsOdd (row0705.map Prod.snd) oddDots0705 641 10 = true := by
  decide +kernel

theorem evenSum0706_checked :
    packedSumCheck packedFactorsEven (row0706.map Prod.fst) evenDots0706 641 10 = true := by
  decide +kernel

theorem oddSum0706_checked :
    packedSumCheck packedFactorsOdd (row0706.map Prod.snd) oddDots0706 641 10 = true := by
  decide +kernel

theorem evenSum0707_checked :
    packedSumCheck packedFactorsEven (row0707.map Prod.fst) evenDots0707 641 10 = true := by
  decide +kernel

theorem oddSum0707_checked :
    packedSumCheck packedFactorsOdd (row0707.map Prod.snd) oddDots0707 641 10 = true := by
  decide +kernel

theorem evenSum0708_checked :
    packedSumCheck packedFactorsEven (row0708.map Prod.fst) evenDots0708 641 10 = true := by
  decide +kernel

theorem oddSum0708_checked :
    packedSumCheck packedFactorsOdd (row0708.map Prod.snd) oddDots0708 641 10 = true := by
  decide +kernel

theorem evenSum0709_checked :
    packedSumCheck packedFactorsEven (row0709.map Prod.fst) evenDots0709 641 10 = true := by
  decide +kernel

theorem oddSum0709_checked :
    packedSumCheck packedFactorsOdd (row0709.map Prod.snd) oddDots0709 641 10 = true := by
  decide +kernel

theorem evenSum0710_checked :
    packedSumCheck packedFactorsEven (row0710.map Prod.fst) evenDots0710 641 10 = true := by
  decide +kernel

theorem oddSum0710_checked :
    packedSumCheck packedFactorsOdd (row0710.map Prod.snd) oddDots0710 641 10 = true := by
  decide +kernel

theorem evenSum0711_checked :
    packedSumCheck packedFactorsEven (row0711.map Prod.fst) evenDots0711 641 10 = true := by
  decide +kernel

theorem oddSum0711_checked :
    packedSumCheck packedFactorsOdd (row0711.map Prod.snd) oddDots0711 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
