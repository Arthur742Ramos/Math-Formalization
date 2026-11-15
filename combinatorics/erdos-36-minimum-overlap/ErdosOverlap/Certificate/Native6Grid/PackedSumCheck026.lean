module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows026
public import ErdosOverlap.Certificate.Native6Grid.PackedDots026

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0208_checked :
    packedSumCheck packedFactorsEven (row0208.map Prod.fst) evenDots0208 641 10 = true := by
  decide +kernel

theorem oddSum0208_checked :
    packedSumCheck packedFactorsOdd (row0208.map Prod.snd) oddDots0208 641 10 = true := by
  decide +kernel

theorem evenSum0209_checked :
    packedSumCheck packedFactorsEven (row0209.map Prod.fst) evenDots0209 641 10 = true := by
  decide +kernel

theorem oddSum0209_checked :
    packedSumCheck packedFactorsOdd (row0209.map Prod.snd) oddDots0209 641 10 = true := by
  decide +kernel

theorem evenSum0210_checked :
    packedSumCheck packedFactorsEven (row0210.map Prod.fst) evenDots0210 641 10 = true := by
  decide +kernel

theorem oddSum0210_checked :
    packedSumCheck packedFactorsOdd (row0210.map Prod.snd) oddDots0210 641 10 = true := by
  decide +kernel

theorem evenSum0211_checked :
    packedSumCheck packedFactorsEven (row0211.map Prod.fst) evenDots0211 641 10 = true := by
  decide +kernel

theorem oddSum0211_checked :
    packedSumCheck packedFactorsOdd (row0211.map Prod.snd) oddDots0211 641 10 = true := by
  decide +kernel

theorem evenSum0212_checked :
    packedSumCheck packedFactorsEven (row0212.map Prod.fst) evenDots0212 641 10 = true := by
  decide +kernel

theorem oddSum0212_checked :
    packedSumCheck packedFactorsOdd (row0212.map Prod.snd) oddDots0212 641 10 = true := by
  decide +kernel

theorem evenSum0213_checked :
    packedSumCheck packedFactorsEven (row0213.map Prod.fst) evenDots0213 641 10 = true := by
  decide +kernel

theorem oddSum0213_checked :
    packedSumCheck packedFactorsOdd (row0213.map Prod.snd) oddDots0213 641 10 = true := by
  decide +kernel

theorem evenSum0214_checked :
    packedSumCheck packedFactorsEven (row0214.map Prod.fst) evenDots0214 641 10 = true := by
  decide +kernel

theorem oddSum0214_checked :
    packedSumCheck packedFactorsOdd (row0214.map Prod.snd) oddDots0214 641 10 = true := by
  decide +kernel

theorem evenSum0215_checked :
    packedSumCheck packedFactorsEven (row0215.map Prod.fst) evenDots0215 641 10 = true := by
  decide +kernel

theorem oddSum0215_checked :
    packedSumCheck packedFactorsOdd (row0215.map Prod.snd) oddDots0215 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
