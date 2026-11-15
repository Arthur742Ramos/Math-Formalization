module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows017
public import ErdosOverlap.Certificate.Native6Grid.PackedDots017

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0136_checked :
    packedSumCheck packedFactorsEven (row0136.map Prod.fst) evenDots0136 641 10 = true := by
  decide +kernel

theorem oddSum0136_checked :
    packedSumCheck packedFactorsOdd (row0136.map Prod.snd) oddDots0136 641 10 = true := by
  decide +kernel

theorem evenSum0137_checked :
    packedSumCheck packedFactorsEven (row0137.map Prod.fst) evenDots0137 641 10 = true := by
  decide +kernel

theorem oddSum0137_checked :
    packedSumCheck packedFactorsOdd (row0137.map Prod.snd) oddDots0137 641 10 = true := by
  decide +kernel

theorem evenSum0138_checked :
    packedSumCheck packedFactorsEven (row0138.map Prod.fst) evenDots0138 641 10 = true := by
  decide +kernel

theorem oddSum0138_checked :
    packedSumCheck packedFactorsOdd (row0138.map Prod.snd) oddDots0138 641 10 = true := by
  decide +kernel

theorem evenSum0139_checked :
    packedSumCheck packedFactorsEven (row0139.map Prod.fst) evenDots0139 641 10 = true := by
  decide +kernel

theorem oddSum0139_checked :
    packedSumCheck packedFactorsOdd (row0139.map Prod.snd) oddDots0139 641 10 = true := by
  decide +kernel

theorem evenSum0140_checked :
    packedSumCheck packedFactorsEven (row0140.map Prod.fst) evenDots0140 641 10 = true := by
  decide +kernel

theorem oddSum0140_checked :
    packedSumCheck packedFactorsOdd (row0140.map Prod.snd) oddDots0140 641 10 = true := by
  decide +kernel

theorem evenSum0141_checked :
    packedSumCheck packedFactorsEven (row0141.map Prod.fst) evenDots0141 641 10 = true := by
  decide +kernel

theorem oddSum0141_checked :
    packedSumCheck packedFactorsOdd (row0141.map Prod.snd) oddDots0141 641 10 = true := by
  decide +kernel

theorem evenSum0142_checked :
    packedSumCheck packedFactorsEven (row0142.map Prod.fst) evenDots0142 641 10 = true := by
  decide +kernel

theorem oddSum0142_checked :
    packedSumCheck packedFactorsOdd (row0142.map Prod.snd) oddDots0142 641 10 = true := by
  decide +kernel

theorem evenSum0143_checked :
    packedSumCheck packedFactorsEven (row0143.map Prod.fst) evenDots0143 641 10 = true := by
  decide +kernel

theorem oddSum0143_checked :
    packedSumCheck packedFactorsOdd (row0143.map Prod.snd) oddDots0143 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
