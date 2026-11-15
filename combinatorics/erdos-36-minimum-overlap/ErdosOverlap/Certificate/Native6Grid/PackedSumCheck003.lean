module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows003
public import ErdosOverlap.Certificate.Native6Grid.PackedDots003

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0024_checked :
    packedSumCheck packedFactorsEven (row0024.map Prod.fst) evenDots0024 641 10 = true := by
  decide +kernel

theorem oddSum0024_checked :
    packedSumCheck packedFactorsOdd (row0024.map Prod.snd) oddDots0024 641 10 = true := by
  decide +kernel

theorem evenSum0025_checked :
    packedSumCheck packedFactorsEven (row0025.map Prod.fst) evenDots0025 641 10 = true := by
  decide +kernel

theorem oddSum0025_checked :
    packedSumCheck packedFactorsOdd (row0025.map Prod.snd) oddDots0025 641 10 = true := by
  decide +kernel

theorem evenSum0026_checked :
    packedSumCheck packedFactorsEven (row0026.map Prod.fst) evenDots0026 641 10 = true := by
  decide +kernel

theorem oddSum0026_checked :
    packedSumCheck packedFactorsOdd (row0026.map Prod.snd) oddDots0026 641 10 = true := by
  decide +kernel

theorem evenSum0027_checked :
    packedSumCheck packedFactorsEven (row0027.map Prod.fst) evenDots0027 641 10 = true := by
  decide +kernel

theorem oddSum0027_checked :
    packedSumCheck packedFactorsOdd (row0027.map Prod.snd) oddDots0027 641 10 = true := by
  decide +kernel

theorem evenSum0028_checked :
    packedSumCheck packedFactorsEven (row0028.map Prod.fst) evenDots0028 641 10 = true := by
  decide +kernel

theorem oddSum0028_checked :
    packedSumCheck packedFactorsOdd (row0028.map Prod.snd) oddDots0028 641 10 = true := by
  decide +kernel

theorem evenSum0029_checked :
    packedSumCheck packedFactorsEven (row0029.map Prod.fst) evenDots0029 641 10 = true := by
  decide +kernel

theorem oddSum0029_checked :
    packedSumCheck packedFactorsOdd (row0029.map Prod.snd) oddDots0029 641 10 = true := by
  decide +kernel

theorem evenSum0030_checked :
    packedSumCheck packedFactorsEven (row0030.map Prod.fst) evenDots0030 641 10 = true := by
  decide +kernel

theorem oddSum0030_checked :
    packedSumCheck packedFactorsOdd (row0030.map Prod.snd) oddDots0030 641 10 = true := by
  decide +kernel

theorem evenSum0031_checked :
    packedSumCheck packedFactorsEven (row0031.map Prod.fst) evenDots0031 641 10 = true := by
  decide +kernel

theorem oddSum0031_checked :
    packedSumCheck packedFactorsOdd (row0031.map Prod.snd) oddDots0031 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
