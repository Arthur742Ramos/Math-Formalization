module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows121
public import ErdosOverlap.Certificate.Native6Grid.PackedDots121

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0968_checked :
    packedSumCheck packedFactorsEven (row0968.map Prod.fst) evenDots0968 641 10 = true := by
  decide +kernel

theorem oddSum0968_checked :
    packedSumCheck packedFactorsOdd (row0968.map Prod.snd) oddDots0968 641 10 = true := by
  decide +kernel

theorem evenSum0969_checked :
    packedSumCheck packedFactorsEven (row0969.map Prod.fst) evenDots0969 641 10 = true := by
  decide +kernel

theorem oddSum0969_checked :
    packedSumCheck packedFactorsOdd (row0969.map Prod.snd) oddDots0969 641 10 = true := by
  decide +kernel

theorem evenSum0970_checked :
    packedSumCheck packedFactorsEven (row0970.map Prod.fst) evenDots0970 641 10 = true := by
  decide +kernel

theorem oddSum0970_checked :
    packedSumCheck packedFactorsOdd (row0970.map Prod.snd) oddDots0970 641 10 = true := by
  decide +kernel

theorem evenSum0971_checked :
    packedSumCheck packedFactorsEven (row0971.map Prod.fst) evenDots0971 641 10 = true := by
  decide +kernel

theorem oddSum0971_checked :
    packedSumCheck packedFactorsOdd (row0971.map Prod.snd) oddDots0971 641 10 = true := by
  decide +kernel

theorem evenSum0972_checked :
    packedSumCheck packedFactorsEven (row0972.map Prod.fst) evenDots0972 641 10 = true := by
  decide +kernel

theorem oddSum0972_checked :
    packedSumCheck packedFactorsOdd (row0972.map Prod.snd) oddDots0972 641 10 = true := by
  decide +kernel

theorem evenSum0973_checked :
    packedSumCheck packedFactorsEven (row0973.map Prod.fst) evenDots0973 641 10 = true := by
  decide +kernel

theorem oddSum0973_checked :
    packedSumCheck packedFactorsOdd (row0973.map Prod.snd) oddDots0973 641 10 = true := by
  decide +kernel

theorem evenSum0974_checked :
    packedSumCheck packedFactorsEven (row0974.map Prod.fst) evenDots0974 641 10 = true := by
  decide +kernel

theorem oddSum0974_checked :
    packedSumCheck packedFactorsOdd (row0974.map Prod.snd) oddDots0974 641 10 = true := by
  decide +kernel

theorem evenSum0975_checked :
    packedSumCheck packedFactorsEven (row0975.map Prod.fst) evenDots0975 641 10 = true := by
  decide +kernel

theorem oddSum0975_checked :
    packedSumCheck packedFactorsOdd (row0975.map Prod.snd) oddDots0975 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
