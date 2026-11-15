module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows106
public import ErdosOverlap.Certificate.Native6Grid.PackedDots106

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0848_checked :
    packedSumCheck packedFactorsEven (row0848.map Prod.fst) evenDots0848 641 10 = true := by
  decide +kernel

theorem oddSum0848_checked :
    packedSumCheck packedFactorsOdd (row0848.map Prod.snd) oddDots0848 641 10 = true := by
  decide +kernel

theorem evenSum0849_checked :
    packedSumCheck packedFactorsEven (row0849.map Prod.fst) evenDots0849 641 10 = true := by
  decide +kernel

theorem oddSum0849_checked :
    packedSumCheck packedFactorsOdd (row0849.map Prod.snd) oddDots0849 641 10 = true := by
  decide +kernel

theorem evenSum0850_checked :
    packedSumCheck packedFactorsEven (row0850.map Prod.fst) evenDots0850 641 10 = true := by
  decide +kernel

theorem oddSum0850_checked :
    packedSumCheck packedFactorsOdd (row0850.map Prod.snd) oddDots0850 641 10 = true := by
  decide +kernel

theorem evenSum0851_checked :
    packedSumCheck packedFactorsEven (row0851.map Prod.fst) evenDots0851 641 10 = true := by
  decide +kernel

theorem oddSum0851_checked :
    packedSumCheck packedFactorsOdd (row0851.map Prod.snd) oddDots0851 641 10 = true := by
  decide +kernel

theorem evenSum0852_checked :
    packedSumCheck packedFactorsEven (row0852.map Prod.fst) evenDots0852 641 10 = true := by
  decide +kernel

theorem oddSum0852_checked :
    packedSumCheck packedFactorsOdd (row0852.map Prod.snd) oddDots0852 641 10 = true := by
  decide +kernel

theorem evenSum0853_checked :
    packedSumCheck packedFactorsEven (row0853.map Prod.fst) evenDots0853 641 10 = true := by
  decide +kernel

theorem oddSum0853_checked :
    packedSumCheck packedFactorsOdd (row0853.map Prod.snd) oddDots0853 641 10 = true := by
  decide +kernel

theorem evenSum0854_checked :
    packedSumCheck packedFactorsEven (row0854.map Prod.fst) evenDots0854 641 10 = true := by
  decide +kernel

theorem oddSum0854_checked :
    packedSumCheck packedFactorsOdd (row0854.map Prod.snd) oddDots0854 641 10 = true := by
  decide +kernel

theorem evenSum0855_checked :
    packedSumCheck packedFactorsEven (row0855.map Prod.fst) evenDots0855 641 10 = true := by
  decide +kernel

theorem oddSum0855_checked :
    packedSumCheck packedFactorsOdd (row0855.map Prod.snd) oddDots0855 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
