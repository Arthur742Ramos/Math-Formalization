module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows001
public import ErdosOverlap.Certificate.Native6Grid.PackedDots001

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0008_checked :
    packedSumCheck packedFactorsEven (row0008.map Prod.fst) evenDots0008 641 10 = true := by
  decide +kernel

theorem oddSum0008_checked :
    packedSumCheck packedFactorsOdd (row0008.map Prod.snd) oddDots0008 641 10 = true := by
  decide +kernel

theorem evenSum0009_checked :
    packedSumCheck packedFactorsEven (row0009.map Prod.fst) evenDots0009 641 10 = true := by
  decide +kernel

theorem oddSum0009_checked :
    packedSumCheck packedFactorsOdd (row0009.map Prod.snd) oddDots0009 641 10 = true := by
  decide +kernel

theorem evenSum0010_checked :
    packedSumCheck packedFactorsEven (row0010.map Prod.fst) evenDots0010 641 10 = true := by
  decide +kernel

theorem oddSum0010_checked :
    packedSumCheck packedFactorsOdd (row0010.map Prod.snd) oddDots0010 641 10 = true := by
  decide +kernel

theorem evenSum0011_checked :
    packedSumCheck packedFactorsEven (row0011.map Prod.fst) evenDots0011 641 10 = true := by
  decide +kernel

theorem oddSum0011_checked :
    packedSumCheck packedFactorsOdd (row0011.map Prod.snd) oddDots0011 641 10 = true := by
  decide +kernel

theorem evenSum0012_checked :
    packedSumCheck packedFactorsEven (row0012.map Prod.fst) evenDots0012 641 10 = true := by
  decide +kernel

theorem oddSum0012_checked :
    packedSumCheck packedFactorsOdd (row0012.map Prod.snd) oddDots0012 641 10 = true := by
  decide +kernel

theorem evenSum0013_checked :
    packedSumCheck packedFactorsEven (row0013.map Prod.fst) evenDots0013 641 10 = true := by
  decide +kernel

theorem oddSum0013_checked :
    packedSumCheck packedFactorsOdd (row0013.map Prod.snd) oddDots0013 641 10 = true := by
  decide +kernel

theorem evenSum0014_checked :
    packedSumCheck packedFactorsEven (row0014.map Prod.fst) evenDots0014 641 10 = true := by
  decide +kernel

theorem oddSum0014_checked :
    packedSumCheck packedFactorsOdd (row0014.map Prod.snd) oddDots0014 641 10 = true := by
  decide +kernel

theorem evenSum0015_checked :
    packedSumCheck packedFactorsEven (row0015.map Prod.fst) evenDots0015 641 10 = true := by
  decide +kernel

theorem oddSum0015_checked :
    packedSumCheck packedFactorsOdd (row0015.map Prod.snd) oddDots0015 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
