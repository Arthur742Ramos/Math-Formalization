module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows040
public import ErdosOverlap.Certificate.Native6Grid.PackedDots040

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0320_checked :
    packedSumCheck packedFactorsEven (row0320.map Prod.fst) evenDots0320 641 10 = true := by
  decide +kernel

theorem oddSum0320_checked :
    packedSumCheck packedFactorsOdd (row0320.map Prod.snd) oddDots0320 641 10 = true := by
  decide +kernel

theorem evenSum0321_checked :
    packedSumCheck packedFactorsEven (row0321.map Prod.fst) evenDots0321 641 10 = true := by
  decide +kernel

theorem oddSum0321_checked :
    packedSumCheck packedFactorsOdd (row0321.map Prod.snd) oddDots0321 641 10 = true := by
  decide +kernel

theorem evenSum0322_checked :
    packedSumCheck packedFactorsEven (row0322.map Prod.fst) evenDots0322 641 10 = true := by
  decide +kernel

theorem oddSum0322_checked :
    packedSumCheck packedFactorsOdd (row0322.map Prod.snd) oddDots0322 641 10 = true := by
  decide +kernel

theorem evenSum0323_checked :
    packedSumCheck packedFactorsEven (row0323.map Prod.fst) evenDots0323 641 10 = true := by
  decide +kernel

theorem oddSum0323_checked :
    packedSumCheck packedFactorsOdd (row0323.map Prod.snd) oddDots0323 641 10 = true := by
  decide +kernel

theorem evenSum0324_checked :
    packedSumCheck packedFactorsEven (row0324.map Prod.fst) evenDots0324 641 10 = true := by
  decide +kernel

theorem oddSum0324_checked :
    packedSumCheck packedFactorsOdd (row0324.map Prod.snd) oddDots0324 641 10 = true := by
  decide +kernel

theorem evenSum0325_checked :
    packedSumCheck packedFactorsEven (row0325.map Prod.fst) evenDots0325 641 10 = true := by
  decide +kernel

theorem oddSum0325_checked :
    packedSumCheck packedFactorsOdd (row0325.map Prod.snd) oddDots0325 641 10 = true := by
  decide +kernel

theorem evenSum0326_checked :
    packedSumCheck packedFactorsEven (row0326.map Prod.fst) evenDots0326 641 10 = true := by
  decide +kernel

theorem oddSum0326_checked :
    packedSumCheck packedFactorsOdd (row0326.map Prod.snd) oddDots0326 641 10 = true := by
  decide +kernel

theorem evenSum0327_checked :
    packedSumCheck packedFactorsEven (row0327.map Prod.fst) evenDots0327 641 10 = true := by
  decide +kernel

theorem oddSum0327_checked :
    packedSumCheck packedFactorsOdd (row0327.map Prod.snd) oddDots0327 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
