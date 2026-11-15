module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows011
public import ErdosOverlap.Certificate.Native6Grid.PackedDots011

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0088_checked :
    packedSumCheck packedFactorsEven (row0088.map Prod.fst) evenDots0088 641 10 = true := by
  decide +kernel

theorem oddSum0088_checked :
    packedSumCheck packedFactorsOdd (row0088.map Prod.snd) oddDots0088 641 10 = true := by
  decide +kernel

theorem evenSum0089_checked :
    packedSumCheck packedFactorsEven (row0089.map Prod.fst) evenDots0089 641 10 = true := by
  decide +kernel

theorem oddSum0089_checked :
    packedSumCheck packedFactorsOdd (row0089.map Prod.snd) oddDots0089 641 10 = true := by
  decide +kernel

theorem evenSum0090_checked :
    packedSumCheck packedFactorsEven (row0090.map Prod.fst) evenDots0090 641 10 = true := by
  decide +kernel

theorem oddSum0090_checked :
    packedSumCheck packedFactorsOdd (row0090.map Prod.snd) oddDots0090 641 10 = true := by
  decide +kernel

theorem evenSum0091_checked :
    packedSumCheck packedFactorsEven (row0091.map Prod.fst) evenDots0091 641 10 = true := by
  decide +kernel

theorem oddSum0091_checked :
    packedSumCheck packedFactorsOdd (row0091.map Prod.snd) oddDots0091 641 10 = true := by
  decide +kernel

theorem evenSum0092_checked :
    packedSumCheck packedFactorsEven (row0092.map Prod.fst) evenDots0092 641 10 = true := by
  decide +kernel

theorem oddSum0092_checked :
    packedSumCheck packedFactorsOdd (row0092.map Prod.snd) oddDots0092 641 10 = true := by
  decide +kernel

theorem evenSum0093_checked :
    packedSumCheck packedFactorsEven (row0093.map Prod.fst) evenDots0093 641 10 = true := by
  decide +kernel

theorem oddSum0093_checked :
    packedSumCheck packedFactorsOdd (row0093.map Prod.snd) oddDots0093 641 10 = true := by
  decide +kernel

theorem evenSum0094_checked :
    packedSumCheck packedFactorsEven (row0094.map Prod.fst) evenDots0094 641 10 = true := by
  decide +kernel

theorem oddSum0094_checked :
    packedSumCheck packedFactorsOdd (row0094.map Prod.snd) oddDots0094 641 10 = true := by
  decide +kernel

theorem evenSum0095_checked :
    packedSumCheck packedFactorsEven (row0095.map Prod.fst) evenDots0095 641 10 = true := by
  decide +kernel

theorem oddSum0095_checked :
    packedSumCheck packedFactorsOdd (row0095.map Prod.snd) oddDots0095 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
