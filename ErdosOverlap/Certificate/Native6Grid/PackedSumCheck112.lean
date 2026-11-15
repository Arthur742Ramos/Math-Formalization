module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows112
public import ErdosOverlap.Certificate.Native6Grid.PackedDots112

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0896_checked :
    packedSumCheck packedFactorsEven (row0896.map Prod.fst) evenDots0896 641 10 = true := by
  decide +kernel

theorem oddSum0896_checked :
    packedSumCheck packedFactorsOdd (row0896.map Prod.snd) oddDots0896 641 10 = true := by
  decide +kernel

theorem evenSum0897_checked :
    packedSumCheck packedFactorsEven (row0897.map Prod.fst) evenDots0897 641 10 = true := by
  decide +kernel

theorem oddSum0897_checked :
    packedSumCheck packedFactorsOdd (row0897.map Prod.snd) oddDots0897 641 10 = true := by
  decide +kernel

theorem evenSum0898_checked :
    packedSumCheck packedFactorsEven (row0898.map Prod.fst) evenDots0898 641 10 = true := by
  decide +kernel

theorem oddSum0898_checked :
    packedSumCheck packedFactorsOdd (row0898.map Prod.snd) oddDots0898 641 10 = true := by
  decide +kernel

theorem evenSum0899_checked :
    packedSumCheck packedFactorsEven (row0899.map Prod.fst) evenDots0899 641 10 = true := by
  decide +kernel

theorem oddSum0899_checked :
    packedSumCheck packedFactorsOdd (row0899.map Prod.snd) oddDots0899 641 10 = true := by
  decide +kernel

theorem evenSum0900_checked :
    packedSumCheck packedFactorsEven (row0900.map Prod.fst) evenDots0900 641 10 = true := by
  decide +kernel

theorem oddSum0900_checked :
    packedSumCheck packedFactorsOdd (row0900.map Prod.snd) oddDots0900 641 10 = true := by
  decide +kernel

theorem evenSum0901_checked :
    packedSumCheck packedFactorsEven (row0901.map Prod.fst) evenDots0901 641 10 = true := by
  decide +kernel

theorem oddSum0901_checked :
    packedSumCheck packedFactorsOdd (row0901.map Prod.snd) oddDots0901 641 10 = true := by
  decide +kernel

theorem evenSum0902_checked :
    packedSumCheck packedFactorsEven (row0902.map Prod.fst) evenDots0902 641 10 = true := by
  decide +kernel

theorem oddSum0902_checked :
    packedSumCheck packedFactorsOdd (row0902.map Prod.snd) oddDots0902 641 10 = true := by
  decide +kernel

theorem evenSum0903_checked :
    packedSumCheck packedFactorsEven (row0903.map Prod.fst) evenDots0903 641 10 = true := by
  decide +kernel

theorem oddSum0903_checked :
    packedSumCheck packedFactorsOdd (row0903.map Prod.snd) oddDots0903 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
