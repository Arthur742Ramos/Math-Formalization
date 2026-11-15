module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows116
public import ErdosOverlap.Certificate.Native6Grid.PackedDots116

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0928_checked :
    packedSumCheck packedFactorsEven (row0928.map Prod.fst) evenDots0928 641 10 = true := by
  decide +kernel

theorem oddSum0928_checked :
    packedSumCheck packedFactorsOdd (row0928.map Prod.snd) oddDots0928 641 10 = true := by
  decide +kernel

theorem evenSum0929_checked :
    packedSumCheck packedFactorsEven (row0929.map Prod.fst) evenDots0929 641 10 = true := by
  decide +kernel

theorem oddSum0929_checked :
    packedSumCheck packedFactorsOdd (row0929.map Prod.snd) oddDots0929 641 10 = true := by
  decide +kernel

theorem evenSum0930_checked :
    packedSumCheck packedFactorsEven (row0930.map Prod.fst) evenDots0930 641 10 = true := by
  decide +kernel

theorem oddSum0930_checked :
    packedSumCheck packedFactorsOdd (row0930.map Prod.snd) oddDots0930 641 10 = true := by
  decide +kernel

theorem evenSum0931_checked :
    packedSumCheck packedFactorsEven (row0931.map Prod.fst) evenDots0931 641 10 = true := by
  decide +kernel

theorem oddSum0931_checked :
    packedSumCheck packedFactorsOdd (row0931.map Prod.snd) oddDots0931 641 10 = true := by
  decide +kernel

theorem evenSum0932_checked :
    packedSumCheck packedFactorsEven (row0932.map Prod.fst) evenDots0932 641 10 = true := by
  decide +kernel

theorem oddSum0932_checked :
    packedSumCheck packedFactorsOdd (row0932.map Prod.snd) oddDots0932 641 10 = true := by
  decide +kernel

theorem evenSum0933_checked :
    packedSumCheck packedFactorsEven (row0933.map Prod.fst) evenDots0933 641 10 = true := by
  decide +kernel

theorem oddSum0933_checked :
    packedSumCheck packedFactorsOdd (row0933.map Prod.snd) oddDots0933 641 10 = true := by
  decide +kernel

theorem evenSum0934_checked :
    packedSumCheck packedFactorsEven (row0934.map Prod.fst) evenDots0934 641 10 = true := by
  decide +kernel

theorem oddSum0934_checked :
    packedSumCheck packedFactorsOdd (row0934.map Prod.snd) oddDots0934 641 10 = true := by
  decide +kernel

theorem evenSum0935_checked :
    packedSumCheck packedFactorsEven (row0935.map Prod.fst) evenDots0935 641 10 = true := by
  decide +kernel

theorem oddSum0935_checked :
    packedSumCheck packedFactorsOdd (row0935.map Prod.snd) oddDots0935 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
