module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows031
public import ErdosOverlap.Certificate.Native6Grid.PackedDots031

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0248_checked :
    packedSumCheck packedFactorsEven (row0248.map Prod.fst) evenDots0248 641 10 = true := by
  decide +kernel

theorem oddSum0248_checked :
    packedSumCheck packedFactorsOdd (row0248.map Prod.snd) oddDots0248 641 10 = true := by
  decide +kernel

theorem evenSum0249_checked :
    packedSumCheck packedFactorsEven (row0249.map Prod.fst) evenDots0249 641 10 = true := by
  decide +kernel

theorem oddSum0249_checked :
    packedSumCheck packedFactorsOdd (row0249.map Prod.snd) oddDots0249 641 10 = true := by
  decide +kernel

theorem evenSum0250_checked :
    packedSumCheck packedFactorsEven (row0250.map Prod.fst) evenDots0250 641 10 = true := by
  decide +kernel

theorem oddSum0250_checked :
    packedSumCheck packedFactorsOdd (row0250.map Prod.snd) oddDots0250 641 10 = true := by
  decide +kernel

theorem evenSum0251_checked :
    packedSumCheck packedFactorsEven (row0251.map Prod.fst) evenDots0251 641 10 = true := by
  decide +kernel

theorem oddSum0251_checked :
    packedSumCheck packedFactorsOdd (row0251.map Prod.snd) oddDots0251 641 10 = true := by
  decide +kernel

theorem evenSum0252_checked :
    packedSumCheck packedFactorsEven (row0252.map Prod.fst) evenDots0252 641 10 = true := by
  decide +kernel

theorem oddSum0252_checked :
    packedSumCheck packedFactorsOdd (row0252.map Prod.snd) oddDots0252 641 10 = true := by
  decide +kernel

theorem evenSum0253_checked :
    packedSumCheck packedFactorsEven (row0253.map Prod.fst) evenDots0253 641 10 = true := by
  decide +kernel

theorem oddSum0253_checked :
    packedSumCheck packedFactorsOdd (row0253.map Prod.snd) oddDots0253 641 10 = true := by
  decide +kernel

theorem evenSum0254_checked :
    packedSumCheck packedFactorsEven (row0254.map Prod.fst) evenDots0254 641 10 = true := by
  decide +kernel

theorem oddSum0254_checked :
    packedSumCheck packedFactorsOdd (row0254.map Prod.snd) oddDots0254 641 10 = true := by
  decide +kernel

theorem evenSum0255_checked :
    packedSumCheck packedFactorsEven (row0255.map Prod.fst) evenDots0255 641 10 = true := by
  decide +kernel

theorem oddSum0255_checked :
    packedSumCheck packedFactorsOdd (row0255.map Prod.snd) oddDots0255 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
