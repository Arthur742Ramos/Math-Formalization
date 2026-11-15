module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows048
public import ErdosOverlap.Certificate.Native6Grid.PackedDots048

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0384_checked :
    packedSumCheck packedFactorsEven (row0384.map Prod.fst) evenDots0384 641 10 = true := by
  decide +kernel

theorem oddSum0384_checked :
    packedSumCheck packedFactorsOdd (row0384.map Prod.snd) oddDots0384 641 10 = true := by
  decide +kernel

theorem evenSum0385_checked :
    packedSumCheck packedFactorsEven (row0385.map Prod.fst) evenDots0385 641 10 = true := by
  decide +kernel

theorem oddSum0385_checked :
    packedSumCheck packedFactorsOdd (row0385.map Prod.snd) oddDots0385 641 10 = true := by
  decide +kernel

theorem evenSum0386_checked :
    packedSumCheck packedFactorsEven (row0386.map Prod.fst) evenDots0386 641 10 = true := by
  decide +kernel

theorem oddSum0386_checked :
    packedSumCheck packedFactorsOdd (row0386.map Prod.snd) oddDots0386 641 10 = true := by
  decide +kernel

theorem evenSum0387_checked :
    packedSumCheck packedFactorsEven (row0387.map Prod.fst) evenDots0387 641 10 = true := by
  decide +kernel

theorem oddSum0387_checked :
    packedSumCheck packedFactorsOdd (row0387.map Prod.snd) oddDots0387 641 10 = true := by
  decide +kernel

theorem evenSum0388_checked :
    packedSumCheck packedFactorsEven (row0388.map Prod.fst) evenDots0388 641 10 = true := by
  decide +kernel

theorem oddSum0388_checked :
    packedSumCheck packedFactorsOdd (row0388.map Prod.snd) oddDots0388 641 10 = true := by
  decide +kernel

theorem evenSum0389_checked :
    packedSumCheck packedFactorsEven (row0389.map Prod.fst) evenDots0389 641 10 = true := by
  decide +kernel

theorem oddSum0389_checked :
    packedSumCheck packedFactorsOdd (row0389.map Prod.snd) oddDots0389 641 10 = true := by
  decide +kernel

theorem evenSum0390_checked :
    packedSumCheck packedFactorsEven (row0390.map Prod.fst) evenDots0390 641 10 = true := by
  decide +kernel

theorem oddSum0390_checked :
    packedSumCheck packedFactorsOdd (row0390.map Prod.snd) oddDots0390 641 10 = true := by
  decide +kernel

theorem evenSum0391_checked :
    packedSumCheck packedFactorsEven (row0391.map Prod.fst) evenDots0391 641 10 = true := by
  decide +kernel

theorem oddSum0391_checked :
    packedSumCheck packedFactorsOdd (row0391.map Prod.snd) oddDots0391 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
