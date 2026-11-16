module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows037
public import ErdosOverlap.Certificate.Native6Grid.PackedDots037

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0296_checked :
    packedSumCheck packedFactorsEven (row0296.map Prod.fst) evenDots0296 641 10 = true := by
  decide +kernel

theorem oddSum0296_checked :
    packedSumCheck packedFactorsOdd (row0296.map Prod.snd) oddDots0296 641 10 = true := by
  decide +kernel

theorem evenSum0297_checked :
    packedSumCheck packedFactorsEven (row0297.map Prod.fst) evenDots0297 641 10 = true := by
  decide +kernel

theorem oddSum0297_checked :
    packedSumCheck packedFactorsOdd (row0297.map Prod.snd) oddDots0297 641 10 = true := by
  decide +kernel

theorem evenSum0298_checked :
    packedSumCheck packedFactorsEven (row0298.map Prod.fst) evenDots0298 641 10 = true := by
  decide +kernel

theorem oddSum0298_checked :
    packedSumCheck packedFactorsOdd (row0298.map Prod.snd) oddDots0298 641 10 = true := by
  decide +kernel

theorem evenSum0299_checked :
    packedSumCheck packedFactorsEven (row0299.map Prod.fst) evenDots0299 641 10 = true := by
  decide +kernel

theorem oddSum0299_checked :
    packedSumCheck packedFactorsOdd (row0299.map Prod.snd) oddDots0299 641 10 = true := by
  decide +kernel

theorem evenSum0300_checked :
    packedSumCheck packedFactorsEven (row0300.map Prod.fst) evenDots0300 641 10 = true := by
  decide +kernel

theorem oddSum0300_checked :
    packedSumCheck packedFactorsOdd (row0300.map Prod.snd) oddDots0300 641 10 = true := by
  decide +kernel

theorem evenSum0301_checked :
    packedSumCheck packedFactorsEven (row0301.map Prod.fst) evenDots0301 641 10 = true := by
  decide +kernel

theorem oddSum0301_checked :
    packedSumCheck packedFactorsOdd (row0301.map Prod.snd) oddDots0301 641 10 = true := by
  decide +kernel

theorem evenSum0302_checked :
    packedSumCheck packedFactorsEven (row0302.map Prod.fst) evenDots0302 641 10 = true := by
  decide +kernel

theorem oddSum0302_checked :
    packedSumCheck packedFactorsOdd (row0302.map Prod.snd) oddDots0302 641 10 = true := by
  decide +kernel

theorem evenSum0303_checked :
    packedSumCheck packedFactorsEven (row0303.map Prod.fst) evenDots0303 641 10 = true := by
  decide +kernel

theorem oddSum0303_checked :
    packedSumCheck packedFactorsOdd (row0303.map Prod.snd) oddDots0303 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
