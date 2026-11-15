module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows005
public import ErdosOverlap.Certificate.Native6Grid.PackedDots005

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0040_checked :
    packedSumCheck packedFactorsEven (row0040.map Prod.fst) evenDots0040 641 10 = true := by
  decide +kernel

theorem oddSum0040_checked :
    packedSumCheck packedFactorsOdd (row0040.map Prod.snd) oddDots0040 641 10 = true := by
  decide +kernel

theorem evenSum0041_checked :
    packedSumCheck packedFactorsEven (row0041.map Prod.fst) evenDots0041 641 10 = true := by
  decide +kernel

theorem oddSum0041_checked :
    packedSumCheck packedFactorsOdd (row0041.map Prod.snd) oddDots0041 641 10 = true := by
  decide +kernel

theorem evenSum0042_checked :
    packedSumCheck packedFactorsEven (row0042.map Prod.fst) evenDots0042 641 10 = true := by
  decide +kernel

theorem oddSum0042_checked :
    packedSumCheck packedFactorsOdd (row0042.map Prod.snd) oddDots0042 641 10 = true := by
  decide +kernel

theorem evenSum0043_checked :
    packedSumCheck packedFactorsEven (row0043.map Prod.fst) evenDots0043 641 10 = true := by
  decide +kernel

theorem oddSum0043_checked :
    packedSumCheck packedFactorsOdd (row0043.map Prod.snd) oddDots0043 641 10 = true := by
  decide +kernel

theorem evenSum0044_checked :
    packedSumCheck packedFactorsEven (row0044.map Prod.fst) evenDots0044 641 10 = true := by
  decide +kernel

theorem oddSum0044_checked :
    packedSumCheck packedFactorsOdd (row0044.map Prod.snd) oddDots0044 641 10 = true := by
  decide +kernel

theorem evenSum0045_checked :
    packedSumCheck packedFactorsEven (row0045.map Prod.fst) evenDots0045 641 10 = true := by
  decide +kernel

theorem oddSum0045_checked :
    packedSumCheck packedFactorsOdd (row0045.map Prod.snd) oddDots0045 641 10 = true := by
  decide +kernel

theorem evenSum0046_checked :
    packedSumCheck packedFactorsEven (row0046.map Prod.fst) evenDots0046 641 10 = true := by
  decide +kernel

theorem oddSum0046_checked :
    packedSumCheck packedFactorsOdd (row0046.map Prod.snd) oddDots0046 641 10 = true := by
  decide +kernel

theorem evenSum0047_checked :
    packedSumCheck packedFactorsEven (row0047.map Prod.fst) evenDots0047 641 10 = true := by
  decide +kernel

theorem oddSum0047_checked :
    packedSumCheck packedFactorsOdd (row0047.map Prod.snd) oddDots0047 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
