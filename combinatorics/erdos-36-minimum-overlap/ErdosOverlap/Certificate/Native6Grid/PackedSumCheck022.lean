module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows022
public import ErdosOverlap.Certificate.Native6Grid.PackedDots022

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0176_checked :
    packedSumCheck packedFactorsEven (row0176.map Prod.fst) evenDots0176 641 10 = true := by
  decide +kernel

theorem oddSum0176_checked :
    packedSumCheck packedFactorsOdd (row0176.map Prod.snd) oddDots0176 641 10 = true := by
  decide +kernel

theorem evenSum0177_checked :
    packedSumCheck packedFactorsEven (row0177.map Prod.fst) evenDots0177 641 10 = true := by
  decide +kernel

theorem oddSum0177_checked :
    packedSumCheck packedFactorsOdd (row0177.map Prod.snd) oddDots0177 641 10 = true := by
  decide +kernel

theorem evenSum0178_checked :
    packedSumCheck packedFactorsEven (row0178.map Prod.fst) evenDots0178 641 10 = true := by
  decide +kernel

theorem oddSum0178_checked :
    packedSumCheck packedFactorsOdd (row0178.map Prod.snd) oddDots0178 641 10 = true := by
  decide +kernel

theorem evenSum0179_checked :
    packedSumCheck packedFactorsEven (row0179.map Prod.fst) evenDots0179 641 10 = true := by
  decide +kernel

theorem oddSum0179_checked :
    packedSumCheck packedFactorsOdd (row0179.map Prod.snd) oddDots0179 641 10 = true := by
  decide +kernel

theorem evenSum0180_checked :
    packedSumCheck packedFactorsEven (row0180.map Prod.fst) evenDots0180 641 10 = true := by
  decide +kernel

theorem oddSum0180_checked :
    packedSumCheck packedFactorsOdd (row0180.map Prod.snd) oddDots0180 641 10 = true := by
  decide +kernel

theorem evenSum0181_checked :
    packedSumCheck packedFactorsEven (row0181.map Prod.fst) evenDots0181 641 10 = true := by
  decide +kernel

theorem oddSum0181_checked :
    packedSumCheck packedFactorsOdd (row0181.map Prod.snd) oddDots0181 641 10 = true := by
  decide +kernel

theorem evenSum0182_checked :
    packedSumCheck packedFactorsEven (row0182.map Prod.fst) evenDots0182 641 10 = true := by
  decide +kernel

theorem oddSum0182_checked :
    packedSumCheck packedFactorsOdd (row0182.map Prod.snd) oddDots0182 641 10 = true := by
  decide +kernel

theorem evenSum0183_checked :
    packedSumCheck packedFactorsEven (row0183.map Prod.fst) evenDots0183 641 10 = true := by
  decide +kernel

theorem oddSum0183_checked :
    packedSumCheck packedFactorsOdd (row0183.map Prod.snd) oddDots0183 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
