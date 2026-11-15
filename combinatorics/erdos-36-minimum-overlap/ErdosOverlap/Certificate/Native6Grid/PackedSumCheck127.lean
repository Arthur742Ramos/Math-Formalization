module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows127
public import ErdosOverlap.Certificate.Native6Grid.PackedDots127

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum1016_checked :
    packedSumCheck packedFactorsEven (row1016.map Prod.fst) evenDots1016 641 10 = true := by
  decide +kernel

theorem oddSum1016_checked :
    packedSumCheck packedFactorsOdd (row1016.map Prod.snd) oddDots1016 641 10 = true := by
  decide +kernel

theorem evenSum1017_checked :
    packedSumCheck packedFactorsEven (row1017.map Prod.fst) evenDots1017 641 10 = true := by
  decide +kernel

theorem oddSum1017_checked :
    packedSumCheck packedFactorsOdd (row1017.map Prod.snd) oddDots1017 641 10 = true := by
  decide +kernel

theorem evenSum1018_checked :
    packedSumCheck packedFactorsEven (row1018.map Prod.fst) evenDots1018 641 10 = true := by
  decide +kernel

theorem oddSum1018_checked :
    packedSumCheck packedFactorsOdd (row1018.map Prod.snd) oddDots1018 641 10 = true := by
  decide +kernel

theorem evenSum1019_checked :
    packedSumCheck packedFactorsEven (row1019.map Prod.fst) evenDots1019 641 10 = true := by
  decide +kernel

theorem oddSum1019_checked :
    packedSumCheck packedFactorsOdd (row1019.map Prod.snd) oddDots1019 641 10 = true := by
  decide +kernel

theorem evenSum1020_checked :
    packedSumCheck packedFactorsEven (row1020.map Prod.fst) evenDots1020 641 10 = true := by
  decide +kernel

theorem oddSum1020_checked :
    packedSumCheck packedFactorsOdd (row1020.map Prod.snd) oddDots1020 641 10 = true := by
  decide +kernel

theorem evenSum1021_checked :
    packedSumCheck packedFactorsEven (row1021.map Prod.fst) evenDots1021 641 10 = true := by
  decide +kernel

theorem oddSum1021_checked :
    packedSumCheck packedFactorsOdd (row1021.map Prod.snd) oddDots1021 641 10 = true := by
  decide +kernel

theorem evenSum1022_checked :
    packedSumCheck packedFactorsEven (row1022.map Prod.fst) evenDots1022 641 10 = true := by
  decide +kernel

theorem oddSum1022_checked :
    packedSumCheck packedFactorsOdd (row1022.map Prod.snd) oddDots1022 641 10 = true := by
  decide +kernel

theorem evenSum1023_checked :
    packedSumCheck packedFactorsEven (row1023.map Prod.fst) evenDots1023 641 10 = true := by
  decide +kernel

theorem oddSum1023_checked :
    packedSumCheck packedFactorsOdd (row1023.map Prod.snd) oddDots1023 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
