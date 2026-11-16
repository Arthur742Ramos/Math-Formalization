module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows105
public import ErdosOverlap.Certificate.Native6Grid.PackedDots105

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0840_checked :
    packedSumCheck packedFactorsEven (row0840.map Prod.fst) evenDots0840 641 10 = true := by
  decide +kernel

theorem oddSum0840_checked :
    packedSumCheck packedFactorsOdd (row0840.map Prod.snd) oddDots0840 641 10 = true := by
  decide +kernel

theorem evenSum0841_checked :
    packedSumCheck packedFactorsEven (row0841.map Prod.fst) evenDots0841 641 10 = true := by
  decide +kernel

theorem oddSum0841_checked :
    packedSumCheck packedFactorsOdd (row0841.map Prod.snd) oddDots0841 641 10 = true := by
  decide +kernel

theorem evenSum0842_checked :
    packedSumCheck packedFactorsEven (row0842.map Prod.fst) evenDots0842 641 10 = true := by
  decide +kernel

theorem oddSum0842_checked :
    packedSumCheck packedFactorsOdd (row0842.map Prod.snd) oddDots0842 641 10 = true := by
  decide +kernel

theorem evenSum0843_checked :
    packedSumCheck packedFactorsEven (row0843.map Prod.fst) evenDots0843 641 10 = true := by
  decide +kernel

theorem oddSum0843_checked :
    packedSumCheck packedFactorsOdd (row0843.map Prod.snd) oddDots0843 641 10 = true := by
  decide +kernel

theorem evenSum0844_checked :
    packedSumCheck packedFactorsEven (row0844.map Prod.fst) evenDots0844 641 10 = true := by
  decide +kernel

theorem oddSum0844_checked :
    packedSumCheck packedFactorsOdd (row0844.map Prod.snd) oddDots0844 641 10 = true := by
  decide +kernel

theorem evenSum0845_checked :
    packedSumCheck packedFactorsEven (row0845.map Prod.fst) evenDots0845 641 10 = true := by
  decide +kernel

theorem oddSum0845_checked :
    packedSumCheck packedFactorsOdd (row0845.map Prod.snd) oddDots0845 641 10 = true := by
  decide +kernel

theorem evenSum0846_checked :
    packedSumCheck packedFactorsEven (row0846.map Prod.fst) evenDots0846 641 10 = true := by
  decide +kernel

theorem oddSum0846_checked :
    packedSumCheck packedFactorsOdd (row0846.map Prod.snd) oddDots0846 641 10 = true := by
  decide +kernel

theorem evenSum0847_checked :
    packedSumCheck packedFactorsEven (row0847.map Prod.fst) evenDots0847 641 10 = true := by
  decide +kernel

theorem oddSum0847_checked :
    packedSumCheck packedFactorsOdd (row0847.map Prod.snd) oddDots0847 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
