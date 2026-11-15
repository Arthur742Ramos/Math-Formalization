module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows018
public import ErdosOverlap.Certificate.Native6Grid.PackedDots018

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0144_checked :
    packedSumCheck packedFactorsEven (row0144.map Prod.fst) evenDots0144 641 10 = true := by
  decide +kernel

theorem oddSum0144_checked :
    packedSumCheck packedFactorsOdd (row0144.map Prod.snd) oddDots0144 641 10 = true := by
  decide +kernel

theorem evenSum0145_checked :
    packedSumCheck packedFactorsEven (row0145.map Prod.fst) evenDots0145 641 10 = true := by
  decide +kernel

theorem oddSum0145_checked :
    packedSumCheck packedFactorsOdd (row0145.map Prod.snd) oddDots0145 641 10 = true := by
  decide +kernel

theorem evenSum0146_checked :
    packedSumCheck packedFactorsEven (row0146.map Prod.fst) evenDots0146 641 10 = true := by
  decide +kernel

theorem oddSum0146_checked :
    packedSumCheck packedFactorsOdd (row0146.map Prod.snd) oddDots0146 641 10 = true := by
  decide +kernel

theorem evenSum0147_checked :
    packedSumCheck packedFactorsEven (row0147.map Prod.fst) evenDots0147 641 10 = true := by
  decide +kernel

theorem oddSum0147_checked :
    packedSumCheck packedFactorsOdd (row0147.map Prod.snd) oddDots0147 641 10 = true := by
  decide +kernel

theorem evenSum0148_checked :
    packedSumCheck packedFactorsEven (row0148.map Prod.fst) evenDots0148 641 10 = true := by
  decide +kernel

theorem oddSum0148_checked :
    packedSumCheck packedFactorsOdd (row0148.map Prod.snd) oddDots0148 641 10 = true := by
  decide +kernel

theorem evenSum0149_checked :
    packedSumCheck packedFactorsEven (row0149.map Prod.fst) evenDots0149 641 10 = true := by
  decide +kernel

theorem oddSum0149_checked :
    packedSumCheck packedFactorsOdd (row0149.map Prod.snd) oddDots0149 641 10 = true := by
  decide +kernel

theorem evenSum0150_checked :
    packedSumCheck packedFactorsEven (row0150.map Prod.fst) evenDots0150 641 10 = true := by
  decide +kernel

theorem oddSum0150_checked :
    packedSumCheck packedFactorsOdd (row0150.map Prod.snd) oddDots0150 641 10 = true := by
  decide +kernel

theorem evenSum0151_checked :
    packedSumCheck packedFactorsEven (row0151.map Prod.fst) evenDots0151 641 10 = true := by
  decide +kernel

theorem oddSum0151_checked :
    packedSumCheck packedFactorsOdd (row0151.map Prod.snd) oddDots0151 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
