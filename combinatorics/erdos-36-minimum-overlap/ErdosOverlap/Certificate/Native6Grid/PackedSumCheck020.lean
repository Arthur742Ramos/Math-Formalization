module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows020
public import ErdosOverlap.Certificate.Native6Grid.PackedDots020

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0160_checked :
    packedSumCheck packedFactorsEven (row0160.map Prod.fst) evenDots0160 641 10 = true := by
  decide +kernel

theorem oddSum0160_checked :
    packedSumCheck packedFactorsOdd (row0160.map Prod.snd) oddDots0160 641 10 = true := by
  decide +kernel

theorem evenSum0161_checked :
    packedSumCheck packedFactorsEven (row0161.map Prod.fst) evenDots0161 641 10 = true := by
  decide +kernel

theorem oddSum0161_checked :
    packedSumCheck packedFactorsOdd (row0161.map Prod.snd) oddDots0161 641 10 = true := by
  decide +kernel

theorem evenSum0162_checked :
    packedSumCheck packedFactorsEven (row0162.map Prod.fst) evenDots0162 641 10 = true := by
  decide +kernel

theorem oddSum0162_checked :
    packedSumCheck packedFactorsOdd (row0162.map Prod.snd) oddDots0162 641 10 = true := by
  decide +kernel

theorem evenSum0163_checked :
    packedSumCheck packedFactorsEven (row0163.map Prod.fst) evenDots0163 641 10 = true := by
  decide +kernel

theorem oddSum0163_checked :
    packedSumCheck packedFactorsOdd (row0163.map Prod.snd) oddDots0163 641 10 = true := by
  decide +kernel

theorem evenSum0164_checked :
    packedSumCheck packedFactorsEven (row0164.map Prod.fst) evenDots0164 641 10 = true := by
  decide +kernel

theorem oddSum0164_checked :
    packedSumCheck packedFactorsOdd (row0164.map Prod.snd) oddDots0164 641 10 = true := by
  decide +kernel

theorem evenSum0165_checked :
    packedSumCheck packedFactorsEven (row0165.map Prod.fst) evenDots0165 641 10 = true := by
  decide +kernel

theorem oddSum0165_checked :
    packedSumCheck packedFactorsOdd (row0165.map Prod.snd) oddDots0165 641 10 = true := by
  decide +kernel

theorem evenSum0166_checked :
    packedSumCheck packedFactorsEven (row0166.map Prod.fst) evenDots0166 641 10 = true := by
  decide +kernel

theorem oddSum0166_checked :
    packedSumCheck packedFactorsOdd (row0166.map Prod.snd) oddDots0166 641 10 = true := by
  decide +kernel

theorem evenSum0167_checked :
    packedSumCheck packedFactorsEven (row0167.map Prod.fst) evenDots0167 641 10 = true := by
  decide +kernel

theorem oddSum0167_checked :
    packedSumCheck packedFactorsOdd (row0167.map Prod.snd) oddDots0167 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
