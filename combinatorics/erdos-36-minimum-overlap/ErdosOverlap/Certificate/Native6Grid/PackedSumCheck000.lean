module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows000
public import ErdosOverlap.Certificate.Native6Grid.PackedDots000

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0000_checked :
    packedSumCheck packedFactorsEven (row0000.map Prod.fst) evenDots0000 641 10 = true := by
  decide +kernel

theorem oddSum0000_checked :
    packedSumCheck packedFactorsOdd (row0000.map Prod.snd) oddDots0000 641 10 = true := by
  decide +kernel

theorem evenSum0001_checked :
    packedSumCheck packedFactorsEven (row0001.map Prod.fst) evenDots0001 641 10 = true := by
  decide +kernel

theorem oddSum0001_checked :
    packedSumCheck packedFactorsOdd (row0001.map Prod.snd) oddDots0001 641 10 = true := by
  decide +kernel

theorem evenSum0002_checked :
    packedSumCheck packedFactorsEven (row0002.map Prod.fst) evenDots0002 641 10 = true := by
  decide +kernel

theorem oddSum0002_checked :
    packedSumCheck packedFactorsOdd (row0002.map Prod.snd) oddDots0002 641 10 = true := by
  decide +kernel

theorem evenSum0003_checked :
    packedSumCheck packedFactorsEven (row0003.map Prod.fst) evenDots0003 641 10 = true := by
  decide +kernel

theorem oddSum0003_checked :
    packedSumCheck packedFactorsOdd (row0003.map Prod.snd) oddDots0003 641 10 = true := by
  decide +kernel

theorem evenSum0004_checked :
    packedSumCheck packedFactorsEven (row0004.map Prod.fst) evenDots0004 641 10 = true := by
  decide +kernel

theorem oddSum0004_checked :
    packedSumCheck packedFactorsOdd (row0004.map Prod.snd) oddDots0004 641 10 = true := by
  decide +kernel

theorem evenSum0005_checked :
    packedSumCheck packedFactorsEven (row0005.map Prod.fst) evenDots0005 641 10 = true := by
  decide +kernel

theorem oddSum0005_checked :
    packedSumCheck packedFactorsOdd (row0005.map Prod.snd) oddDots0005 641 10 = true := by
  decide +kernel

theorem evenSum0006_checked :
    packedSumCheck packedFactorsEven (row0006.map Prod.fst) evenDots0006 641 10 = true := by
  decide +kernel

theorem oddSum0006_checked :
    packedSumCheck packedFactorsOdd (row0006.map Prod.snd) oddDots0006 641 10 = true := by
  decide +kernel

theorem evenSum0007_checked :
    packedSumCheck packedFactorsEven (row0007.map Prod.fst) evenDots0007 641 10 = true := by
  decide +kernel

theorem oddSum0007_checked :
    packedSumCheck packedFactorsOdd (row0007.map Prod.snd) oddDots0007 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
