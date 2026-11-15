module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows114
public import ErdosOverlap.Certificate.Native6Grid.PackedDots114

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0912_checked :
    packedSumCheck packedFactorsEven (row0912.map Prod.fst) evenDots0912 641 10 = true := by
  decide +kernel

theorem oddSum0912_checked :
    packedSumCheck packedFactorsOdd (row0912.map Prod.snd) oddDots0912 641 10 = true := by
  decide +kernel

theorem evenSum0913_checked :
    packedSumCheck packedFactorsEven (row0913.map Prod.fst) evenDots0913 641 10 = true := by
  decide +kernel

theorem oddSum0913_checked :
    packedSumCheck packedFactorsOdd (row0913.map Prod.snd) oddDots0913 641 10 = true := by
  decide +kernel

theorem evenSum0914_checked :
    packedSumCheck packedFactorsEven (row0914.map Prod.fst) evenDots0914 641 10 = true := by
  decide +kernel

theorem oddSum0914_checked :
    packedSumCheck packedFactorsOdd (row0914.map Prod.snd) oddDots0914 641 10 = true := by
  decide +kernel

theorem evenSum0915_checked :
    packedSumCheck packedFactorsEven (row0915.map Prod.fst) evenDots0915 641 10 = true := by
  decide +kernel

theorem oddSum0915_checked :
    packedSumCheck packedFactorsOdd (row0915.map Prod.snd) oddDots0915 641 10 = true := by
  decide +kernel

theorem evenSum0916_checked :
    packedSumCheck packedFactorsEven (row0916.map Prod.fst) evenDots0916 641 10 = true := by
  decide +kernel

theorem oddSum0916_checked :
    packedSumCheck packedFactorsOdd (row0916.map Prod.snd) oddDots0916 641 10 = true := by
  decide +kernel

theorem evenSum0917_checked :
    packedSumCheck packedFactorsEven (row0917.map Prod.fst) evenDots0917 641 10 = true := by
  decide +kernel

theorem oddSum0917_checked :
    packedSumCheck packedFactorsOdd (row0917.map Prod.snd) oddDots0917 641 10 = true := by
  decide +kernel

theorem evenSum0918_checked :
    packedSumCheck packedFactorsEven (row0918.map Prod.fst) evenDots0918 641 10 = true := by
  decide +kernel

theorem oddSum0918_checked :
    packedSumCheck packedFactorsOdd (row0918.map Prod.snd) oddDots0918 641 10 = true := by
  decide +kernel

theorem evenSum0919_checked :
    packedSumCheck packedFactorsEven (row0919.map Prod.fst) evenDots0919 641 10 = true := by
  decide +kernel

theorem oddSum0919_checked :
    packedSumCheck packedFactorsOdd (row0919.map Prod.snd) oddDots0919 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
