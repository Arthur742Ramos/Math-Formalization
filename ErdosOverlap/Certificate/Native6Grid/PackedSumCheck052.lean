module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows052
public import ErdosOverlap.Certificate.Native6Grid.PackedDots052

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0416_checked :
    packedSumCheck packedFactorsEven (row0416.map Prod.fst) evenDots0416 641 10 = true := by
  decide +kernel

theorem oddSum0416_checked :
    packedSumCheck packedFactorsOdd (row0416.map Prod.snd) oddDots0416 641 10 = true := by
  decide +kernel

theorem evenSum0417_checked :
    packedSumCheck packedFactorsEven (row0417.map Prod.fst) evenDots0417 641 10 = true := by
  decide +kernel

theorem oddSum0417_checked :
    packedSumCheck packedFactorsOdd (row0417.map Prod.snd) oddDots0417 641 10 = true := by
  decide +kernel

theorem evenSum0418_checked :
    packedSumCheck packedFactorsEven (row0418.map Prod.fst) evenDots0418 641 10 = true := by
  decide +kernel

theorem oddSum0418_checked :
    packedSumCheck packedFactorsOdd (row0418.map Prod.snd) oddDots0418 641 10 = true := by
  decide +kernel

theorem evenSum0419_checked :
    packedSumCheck packedFactorsEven (row0419.map Prod.fst) evenDots0419 641 10 = true := by
  decide +kernel

theorem oddSum0419_checked :
    packedSumCheck packedFactorsOdd (row0419.map Prod.snd) oddDots0419 641 10 = true := by
  decide +kernel

theorem evenSum0420_checked :
    packedSumCheck packedFactorsEven (row0420.map Prod.fst) evenDots0420 641 10 = true := by
  decide +kernel

theorem oddSum0420_checked :
    packedSumCheck packedFactorsOdd (row0420.map Prod.snd) oddDots0420 641 10 = true := by
  decide +kernel

theorem evenSum0421_checked :
    packedSumCheck packedFactorsEven (row0421.map Prod.fst) evenDots0421 641 10 = true := by
  decide +kernel

theorem oddSum0421_checked :
    packedSumCheck packedFactorsOdd (row0421.map Prod.snd) oddDots0421 641 10 = true := by
  decide +kernel

theorem evenSum0422_checked :
    packedSumCheck packedFactorsEven (row0422.map Prod.fst) evenDots0422 641 10 = true := by
  decide +kernel

theorem oddSum0422_checked :
    packedSumCheck packedFactorsOdd (row0422.map Prod.snd) oddDots0422 641 10 = true := by
  decide +kernel

theorem evenSum0423_checked :
    packedSumCheck packedFactorsEven (row0423.map Prod.fst) evenDots0423 641 10 = true := by
  decide +kernel

theorem oddSum0423_checked :
    packedSumCheck packedFactorsOdd (row0423.map Prod.snd) oddDots0423 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
