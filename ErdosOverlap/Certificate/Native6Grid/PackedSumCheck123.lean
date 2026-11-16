module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows123
public import ErdosOverlap.Certificate.Native6Grid.PackedDots123

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0984_checked :
    packedSumCheck packedFactorsEven (row0984.map Prod.fst) evenDots0984 641 10 = true := by
  decide +kernel

theorem oddSum0984_checked :
    packedSumCheck packedFactorsOdd (row0984.map Prod.snd) oddDots0984 641 10 = true := by
  decide +kernel

theorem evenSum0985_checked :
    packedSumCheck packedFactorsEven (row0985.map Prod.fst) evenDots0985 641 10 = true := by
  decide +kernel

theorem oddSum0985_checked :
    packedSumCheck packedFactorsOdd (row0985.map Prod.snd) oddDots0985 641 10 = true := by
  decide +kernel

theorem evenSum0986_checked :
    packedSumCheck packedFactorsEven (row0986.map Prod.fst) evenDots0986 641 10 = true := by
  decide +kernel

theorem oddSum0986_checked :
    packedSumCheck packedFactorsOdd (row0986.map Prod.snd) oddDots0986 641 10 = true := by
  decide +kernel

theorem evenSum0987_checked :
    packedSumCheck packedFactorsEven (row0987.map Prod.fst) evenDots0987 641 10 = true := by
  decide +kernel

theorem oddSum0987_checked :
    packedSumCheck packedFactorsOdd (row0987.map Prod.snd) oddDots0987 641 10 = true := by
  decide +kernel

theorem evenSum0988_checked :
    packedSumCheck packedFactorsEven (row0988.map Prod.fst) evenDots0988 641 10 = true := by
  decide +kernel

theorem oddSum0988_checked :
    packedSumCheck packedFactorsOdd (row0988.map Prod.snd) oddDots0988 641 10 = true := by
  decide +kernel

theorem evenSum0989_checked :
    packedSumCheck packedFactorsEven (row0989.map Prod.fst) evenDots0989 641 10 = true := by
  decide +kernel

theorem oddSum0989_checked :
    packedSumCheck packedFactorsOdd (row0989.map Prod.snd) oddDots0989 641 10 = true := by
  decide +kernel

theorem evenSum0990_checked :
    packedSumCheck packedFactorsEven (row0990.map Prod.fst) evenDots0990 641 10 = true := by
  decide +kernel

theorem oddSum0990_checked :
    packedSumCheck packedFactorsOdd (row0990.map Prod.snd) oddDots0990 641 10 = true := by
  decide +kernel

theorem evenSum0991_checked :
    packedSumCheck packedFactorsEven (row0991.map Prod.fst) evenDots0991 641 10 = true := by
  decide +kernel

theorem oddSum0991_checked :
    packedSumCheck packedFactorsOdd (row0991.map Prod.snd) oddDots0991 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
