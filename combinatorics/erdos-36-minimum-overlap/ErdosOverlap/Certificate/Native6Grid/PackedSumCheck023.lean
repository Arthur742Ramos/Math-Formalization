module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows023
public import ErdosOverlap.Certificate.Native6Grid.PackedDots023

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0184_checked :
    packedSumCheck packedFactorsEven (row0184.map Prod.fst) evenDots0184 641 10 = true := by
  decide +kernel

theorem oddSum0184_checked :
    packedSumCheck packedFactorsOdd (row0184.map Prod.snd) oddDots0184 641 10 = true := by
  decide +kernel

theorem evenSum0185_checked :
    packedSumCheck packedFactorsEven (row0185.map Prod.fst) evenDots0185 641 10 = true := by
  decide +kernel

theorem oddSum0185_checked :
    packedSumCheck packedFactorsOdd (row0185.map Prod.snd) oddDots0185 641 10 = true := by
  decide +kernel

theorem evenSum0186_checked :
    packedSumCheck packedFactorsEven (row0186.map Prod.fst) evenDots0186 641 10 = true := by
  decide +kernel

theorem oddSum0186_checked :
    packedSumCheck packedFactorsOdd (row0186.map Prod.snd) oddDots0186 641 10 = true := by
  decide +kernel

theorem evenSum0187_checked :
    packedSumCheck packedFactorsEven (row0187.map Prod.fst) evenDots0187 641 10 = true := by
  decide +kernel

theorem oddSum0187_checked :
    packedSumCheck packedFactorsOdd (row0187.map Prod.snd) oddDots0187 641 10 = true := by
  decide +kernel

theorem evenSum0188_checked :
    packedSumCheck packedFactorsEven (row0188.map Prod.fst) evenDots0188 641 10 = true := by
  decide +kernel

theorem oddSum0188_checked :
    packedSumCheck packedFactorsOdd (row0188.map Prod.snd) oddDots0188 641 10 = true := by
  decide +kernel

theorem evenSum0189_checked :
    packedSumCheck packedFactorsEven (row0189.map Prod.fst) evenDots0189 641 10 = true := by
  decide +kernel

theorem oddSum0189_checked :
    packedSumCheck packedFactorsOdd (row0189.map Prod.snd) oddDots0189 641 10 = true := by
  decide +kernel

theorem evenSum0190_checked :
    packedSumCheck packedFactorsEven (row0190.map Prod.fst) evenDots0190 641 10 = true := by
  decide +kernel

theorem oddSum0190_checked :
    packedSumCheck packedFactorsOdd (row0190.map Prod.snd) oddDots0190 641 10 = true := by
  decide +kernel

theorem evenSum0191_checked :
    packedSumCheck packedFactorsEven (row0191.map Prod.fst) evenDots0191 641 10 = true := by
  decide +kernel

theorem oddSum0191_checked :
    packedSumCheck packedFactorsOdd (row0191.map Prod.snd) oddDots0191 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
