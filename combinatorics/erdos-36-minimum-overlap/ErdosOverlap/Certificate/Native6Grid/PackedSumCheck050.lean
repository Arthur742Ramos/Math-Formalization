module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows050
public import ErdosOverlap.Certificate.Native6Grid.PackedDots050

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0400_checked :
    packedSumCheck packedFactorsEven (row0400.map Prod.fst) evenDots0400 641 10 = true := by
  decide +kernel

theorem oddSum0400_checked :
    packedSumCheck packedFactorsOdd (row0400.map Prod.snd) oddDots0400 641 10 = true := by
  decide +kernel

theorem evenSum0401_checked :
    packedSumCheck packedFactorsEven (row0401.map Prod.fst) evenDots0401 641 10 = true := by
  decide +kernel

theorem oddSum0401_checked :
    packedSumCheck packedFactorsOdd (row0401.map Prod.snd) oddDots0401 641 10 = true := by
  decide +kernel

theorem evenSum0402_checked :
    packedSumCheck packedFactorsEven (row0402.map Prod.fst) evenDots0402 641 10 = true := by
  decide +kernel

theorem oddSum0402_checked :
    packedSumCheck packedFactorsOdd (row0402.map Prod.snd) oddDots0402 641 10 = true := by
  decide +kernel

theorem evenSum0403_checked :
    packedSumCheck packedFactorsEven (row0403.map Prod.fst) evenDots0403 641 10 = true := by
  decide +kernel

theorem oddSum0403_checked :
    packedSumCheck packedFactorsOdd (row0403.map Prod.snd) oddDots0403 641 10 = true := by
  decide +kernel

theorem evenSum0404_checked :
    packedSumCheck packedFactorsEven (row0404.map Prod.fst) evenDots0404 641 10 = true := by
  decide +kernel

theorem oddSum0404_checked :
    packedSumCheck packedFactorsOdd (row0404.map Prod.snd) oddDots0404 641 10 = true := by
  decide +kernel

theorem evenSum0405_checked :
    packedSumCheck packedFactorsEven (row0405.map Prod.fst) evenDots0405 641 10 = true := by
  decide +kernel

theorem oddSum0405_checked :
    packedSumCheck packedFactorsOdd (row0405.map Prod.snd) oddDots0405 641 10 = true := by
  decide +kernel

theorem evenSum0406_checked :
    packedSumCheck packedFactorsEven (row0406.map Prod.fst) evenDots0406 641 10 = true := by
  decide +kernel

theorem oddSum0406_checked :
    packedSumCheck packedFactorsOdd (row0406.map Prod.snd) oddDots0406 641 10 = true := by
  decide +kernel

theorem evenSum0407_checked :
    packedSumCheck packedFactorsEven (row0407.map Prod.fst) evenDots0407 641 10 = true := by
  decide +kernel

theorem oddSum0407_checked :
    packedSumCheck packedFactorsOdd (row0407.map Prod.snd) oddDots0407 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
