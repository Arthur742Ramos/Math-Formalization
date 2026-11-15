module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows122
public import ErdosOverlap.Certificate.Native6Grid.PackedDots122

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0976_checked :
    packedSumCheck packedFactorsEven (row0976.map Prod.fst) evenDots0976 641 10 = true := by
  decide +kernel

theorem oddSum0976_checked :
    packedSumCheck packedFactorsOdd (row0976.map Prod.snd) oddDots0976 641 10 = true := by
  decide +kernel

theorem evenSum0977_checked :
    packedSumCheck packedFactorsEven (row0977.map Prod.fst) evenDots0977 641 10 = true := by
  decide +kernel

theorem oddSum0977_checked :
    packedSumCheck packedFactorsOdd (row0977.map Prod.snd) oddDots0977 641 10 = true := by
  decide +kernel

theorem evenSum0978_checked :
    packedSumCheck packedFactorsEven (row0978.map Prod.fst) evenDots0978 641 10 = true := by
  decide +kernel

theorem oddSum0978_checked :
    packedSumCheck packedFactorsOdd (row0978.map Prod.snd) oddDots0978 641 10 = true := by
  decide +kernel

theorem evenSum0979_checked :
    packedSumCheck packedFactorsEven (row0979.map Prod.fst) evenDots0979 641 10 = true := by
  decide +kernel

theorem oddSum0979_checked :
    packedSumCheck packedFactorsOdd (row0979.map Prod.snd) oddDots0979 641 10 = true := by
  decide +kernel

theorem evenSum0980_checked :
    packedSumCheck packedFactorsEven (row0980.map Prod.fst) evenDots0980 641 10 = true := by
  decide +kernel

theorem oddSum0980_checked :
    packedSumCheck packedFactorsOdd (row0980.map Prod.snd) oddDots0980 641 10 = true := by
  decide +kernel

theorem evenSum0981_checked :
    packedSumCheck packedFactorsEven (row0981.map Prod.fst) evenDots0981 641 10 = true := by
  decide +kernel

theorem oddSum0981_checked :
    packedSumCheck packedFactorsOdd (row0981.map Prod.snd) oddDots0981 641 10 = true := by
  decide +kernel

theorem evenSum0982_checked :
    packedSumCheck packedFactorsEven (row0982.map Prod.fst) evenDots0982 641 10 = true := by
  decide +kernel

theorem oddSum0982_checked :
    packedSumCheck packedFactorsOdd (row0982.map Prod.snd) oddDots0982 641 10 = true := by
  decide +kernel

theorem evenSum0983_checked :
    packedSumCheck packedFactorsEven (row0983.map Prod.fst) evenDots0983 641 10 = true := by
  decide +kernel

theorem oddSum0983_checked :
    packedSumCheck packedFactorsOdd (row0983.map Prod.snd) oddDots0983 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
