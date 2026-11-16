module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows028
public import ErdosOverlap.Certificate.Native6Grid.PackedDots028

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0224_checked :
    packedSumCheck packedFactorsEven (row0224.map Prod.fst) evenDots0224 641 10 = true := by
  decide +kernel

theorem oddSum0224_checked :
    packedSumCheck packedFactorsOdd (row0224.map Prod.snd) oddDots0224 641 10 = true := by
  decide +kernel

theorem evenSum0225_checked :
    packedSumCheck packedFactorsEven (row0225.map Prod.fst) evenDots0225 641 10 = true := by
  decide +kernel

theorem oddSum0225_checked :
    packedSumCheck packedFactorsOdd (row0225.map Prod.snd) oddDots0225 641 10 = true := by
  decide +kernel

theorem evenSum0226_checked :
    packedSumCheck packedFactorsEven (row0226.map Prod.fst) evenDots0226 641 10 = true := by
  decide +kernel

theorem oddSum0226_checked :
    packedSumCheck packedFactorsOdd (row0226.map Prod.snd) oddDots0226 641 10 = true := by
  decide +kernel

theorem evenSum0227_checked :
    packedSumCheck packedFactorsEven (row0227.map Prod.fst) evenDots0227 641 10 = true := by
  decide +kernel

theorem oddSum0227_checked :
    packedSumCheck packedFactorsOdd (row0227.map Prod.snd) oddDots0227 641 10 = true := by
  decide +kernel

theorem evenSum0228_checked :
    packedSumCheck packedFactorsEven (row0228.map Prod.fst) evenDots0228 641 10 = true := by
  decide +kernel

theorem oddSum0228_checked :
    packedSumCheck packedFactorsOdd (row0228.map Prod.snd) oddDots0228 641 10 = true := by
  decide +kernel

theorem evenSum0229_checked :
    packedSumCheck packedFactorsEven (row0229.map Prod.fst) evenDots0229 641 10 = true := by
  decide +kernel

theorem oddSum0229_checked :
    packedSumCheck packedFactorsOdd (row0229.map Prod.snd) oddDots0229 641 10 = true := by
  decide +kernel

theorem evenSum0230_checked :
    packedSumCheck packedFactorsEven (row0230.map Prod.fst) evenDots0230 641 10 = true := by
  decide +kernel

theorem oddSum0230_checked :
    packedSumCheck packedFactorsOdd (row0230.map Prod.snd) oddDots0230 641 10 = true := by
  decide +kernel

theorem evenSum0231_checked :
    packedSumCheck packedFactorsEven (row0231.map Prod.fst) evenDots0231 641 10 = true := by
  decide +kernel

theorem oddSum0231_checked :
    packedSumCheck packedFactorsOdd (row0231.map Prod.snd) oddDots0231 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
