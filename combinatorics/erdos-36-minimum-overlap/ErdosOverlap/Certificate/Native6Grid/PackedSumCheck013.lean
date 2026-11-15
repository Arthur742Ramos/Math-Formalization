module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows013
public import ErdosOverlap.Certificate.Native6Grid.PackedDots013

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0104_checked :
    packedSumCheck packedFactorsEven (row0104.map Prod.fst) evenDots0104 641 10 = true := by
  decide +kernel

theorem oddSum0104_checked :
    packedSumCheck packedFactorsOdd (row0104.map Prod.snd) oddDots0104 641 10 = true := by
  decide +kernel

theorem evenSum0105_checked :
    packedSumCheck packedFactorsEven (row0105.map Prod.fst) evenDots0105 641 10 = true := by
  decide +kernel

theorem oddSum0105_checked :
    packedSumCheck packedFactorsOdd (row0105.map Prod.snd) oddDots0105 641 10 = true := by
  decide +kernel

theorem evenSum0106_checked :
    packedSumCheck packedFactorsEven (row0106.map Prod.fst) evenDots0106 641 10 = true := by
  decide +kernel

theorem oddSum0106_checked :
    packedSumCheck packedFactorsOdd (row0106.map Prod.snd) oddDots0106 641 10 = true := by
  decide +kernel

theorem evenSum0107_checked :
    packedSumCheck packedFactorsEven (row0107.map Prod.fst) evenDots0107 641 10 = true := by
  decide +kernel

theorem oddSum0107_checked :
    packedSumCheck packedFactorsOdd (row0107.map Prod.snd) oddDots0107 641 10 = true := by
  decide +kernel

theorem evenSum0108_checked :
    packedSumCheck packedFactorsEven (row0108.map Prod.fst) evenDots0108 641 10 = true := by
  decide +kernel

theorem oddSum0108_checked :
    packedSumCheck packedFactorsOdd (row0108.map Prod.snd) oddDots0108 641 10 = true := by
  decide +kernel

theorem evenSum0109_checked :
    packedSumCheck packedFactorsEven (row0109.map Prod.fst) evenDots0109 641 10 = true := by
  decide +kernel

theorem oddSum0109_checked :
    packedSumCheck packedFactorsOdd (row0109.map Prod.snd) oddDots0109 641 10 = true := by
  decide +kernel

theorem evenSum0110_checked :
    packedSumCheck packedFactorsEven (row0110.map Prod.fst) evenDots0110 641 10 = true := by
  decide +kernel

theorem oddSum0110_checked :
    packedSumCheck packedFactorsOdd (row0110.map Prod.snd) oddDots0110 641 10 = true := by
  decide +kernel

theorem evenSum0111_checked :
    packedSumCheck packedFactorsEven (row0111.map Prod.fst) evenDots0111 641 10 = true := by
  decide +kernel

theorem oddSum0111_checked :
    packedSumCheck packedFactorsOdd (row0111.map Prod.snd) oddDots0111 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
