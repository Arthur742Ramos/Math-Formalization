module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows078
public import ErdosOverlap.Certificate.Native6Grid.PackedDots078

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0624_checked :
    packedSumCheck packedFactorsEven (row0624.map Prod.fst) evenDots0624 641 10 = true := by
  decide +kernel

theorem oddSum0624_checked :
    packedSumCheck packedFactorsOdd (row0624.map Prod.snd) oddDots0624 641 10 = true := by
  decide +kernel

theorem evenSum0625_checked :
    packedSumCheck packedFactorsEven (row0625.map Prod.fst) evenDots0625 641 10 = true := by
  decide +kernel

theorem oddSum0625_checked :
    packedSumCheck packedFactorsOdd (row0625.map Prod.snd) oddDots0625 641 10 = true := by
  decide +kernel

theorem evenSum0626_checked :
    packedSumCheck packedFactorsEven (row0626.map Prod.fst) evenDots0626 641 10 = true := by
  decide +kernel

theorem oddSum0626_checked :
    packedSumCheck packedFactorsOdd (row0626.map Prod.snd) oddDots0626 641 10 = true := by
  decide +kernel

theorem evenSum0627_checked :
    packedSumCheck packedFactorsEven (row0627.map Prod.fst) evenDots0627 641 10 = true := by
  decide +kernel

theorem oddSum0627_checked :
    packedSumCheck packedFactorsOdd (row0627.map Prod.snd) oddDots0627 641 10 = true := by
  decide +kernel

theorem evenSum0628_checked :
    packedSumCheck packedFactorsEven (row0628.map Prod.fst) evenDots0628 641 10 = true := by
  decide +kernel

theorem oddSum0628_checked :
    packedSumCheck packedFactorsOdd (row0628.map Prod.snd) oddDots0628 641 10 = true := by
  decide +kernel

theorem evenSum0629_checked :
    packedSumCheck packedFactorsEven (row0629.map Prod.fst) evenDots0629 641 10 = true := by
  decide +kernel

theorem oddSum0629_checked :
    packedSumCheck packedFactorsOdd (row0629.map Prod.snd) oddDots0629 641 10 = true := by
  decide +kernel

theorem evenSum0630_checked :
    packedSumCheck packedFactorsEven (row0630.map Prod.fst) evenDots0630 641 10 = true := by
  decide +kernel

theorem oddSum0630_checked :
    packedSumCheck packedFactorsOdd (row0630.map Prod.snd) oddDots0630 641 10 = true := by
  decide +kernel

theorem evenSum0631_checked :
    packedSumCheck packedFactorsEven (row0631.map Prod.fst) evenDots0631 641 10 = true := by
  decide +kernel

theorem oddSum0631_checked :
    packedSumCheck packedFactorsOdd (row0631.map Prod.snd) oddDots0631 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
