module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows016
public import ErdosOverlap.Certificate.Native6Grid.PackedDots016

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0128_checked :
    packedSumCheck packedFactorsEven (row0128.map Prod.fst) evenDots0128 641 10 = true := by
  decide +kernel

theorem oddSum0128_checked :
    packedSumCheck packedFactorsOdd (row0128.map Prod.snd) oddDots0128 641 10 = true := by
  decide +kernel

theorem evenSum0129_checked :
    packedSumCheck packedFactorsEven (row0129.map Prod.fst) evenDots0129 641 10 = true := by
  decide +kernel

theorem oddSum0129_checked :
    packedSumCheck packedFactorsOdd (row0129.map Prod.snd) oddDots0129 641 10 = true := by
  decide +kernel

theorem evenSum0130_checked :
    packedSumCheck packedFactorsEven (row0130.map Prod.fst) evenDots0130 641 10 = true := by
  decide +kernel

theorem oddSum0130_checked :
    packedSumCheck packedFactorsOdd (row0130.map Prod.snd) oddDots0130 641 10 = true := by
  decide +kernel

theorem evenSum0131_checked :
    packedSumCheck packedFactorsEven (row0131.map Prod.fst) evenDots0131 641 10 = true := by
  decide +kernel

theorem oddSum0131_checked :
    packedSumCheck packedFactorsOdd (row0131.map Prod.snd) oddDots0131 641 10 = true := by
  decide +kernel

theorem evenSum0132_checked :
    packedSumCheck packedFactorsEven (row0132.map Prod.fst) evenDots0132 641 10 = true := by
  decide +kernel

theorem oddSum0132_checked :
    packedSumCheck packedFactorsOdd (row0132.map Prod.snd) oddDots0132 641 10 = true := by
  decide +kernel

theorem evenSum0133_checked :
    packedSumCheck packedFactorsEven (row0133.map Prod.fst) evenDots0133 641 10 = true := by
  decide +kernel

theorem oddSum0133_checked :
    packedSumCheck packedFactorsOdd (row0133.map Prod.snd) oddDots0133 641 10 = true := by
  decide +kernel

theorem evenSum0134_checked :
    packedSumCheck packedFactorsEven (row0134.map Prod.fst) evenDots0134 641 10 = true := by
  decide +kernel

theorem oddSum0134_checked :
    packedSumCheck packedFactorsOdd (row0134.map Prod.snd) oddDots0134 641 10 = true := by
  decide +kernel

theorem evenSum0135_checked :
    packedSumCheck packedFactorsEven (row0135.map Prod.fst) evenDots0135 641 10 = true := by
  decide +kernel

theorem oddSum0135_checked :
    packedSumCheck packedFactorsOdd (row0135.map Prod.snd) oddDots0135 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
