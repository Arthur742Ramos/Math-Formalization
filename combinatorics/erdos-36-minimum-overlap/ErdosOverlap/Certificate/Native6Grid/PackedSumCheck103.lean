module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows103
public import ErdosOverlap.Certificate.Native6Grid.PackedDots103

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0824_checked :
    packedSumCheck packedFactorsEven (row0824.map Prod.fst) evenDots0824 641 10 = true := by
  decide +kernel

theorem oddSum0824_checked :
    packedSumCheck packedFactorsOdd (row0824.map Prod.snd) oddDots0824 641 10 = true := by
  decide +kernel

theorem evenSum0825_checked :
    packedSumCheck packedFactorsEven (row0825.map Prod.fst) evenDots0825 641 10 = true := by
  decide +kernel

theorem oddSum0825_checked :
    packedSumCheck packedFactorsOdd (row0825.map Prod.snd) oddDots0825 641 10 = true := by
  decide +kernel

theorem evenSum0826_checked :
    packedSumCheck packedFactorsEven (row0826.map Prod.fst) evenDots0826 641 10 = true := by
  decide +kernel

theorem oddSum0826_checked :
    packedSumCheck packedFactorsOdd (row0826.map Prod.snd) oddDots0826 641 10 = true := by
  decide +kernel

theorem evenSum0827_checked :
    packedSumCheck packedFactorsEven (row0827.map Prod.fst) evenDots0827 641 10 = true := by
  decide +kernel

theorem oddSum0827_checked :
    packedSumCheck packedFactorsOdd (row0827.map Prod.snd) oddDots0827 641 10 = true := by
  decide +kernel

theorem evenSum0828_checked :
    packedSumCheck packedFactorsEven (row0828.map Prod.fst) evenDots0828 641 10 = true := by
  decide +kernel

theorem oddSum0828_checked :
    packedSumCheck packedFactorsOdd (row0828.map Prod.snd) oddDots0828 641 10 = true := by
  decide +kernel

theorem evenSum0829_checked :
    packedSumCheck packedFactorsEven (row0829.map Prod.fst) evenDots0829 641 10 = true := by
  decide +kernel

theorem oddSum0829_checked :
    packedSumCheck packedFactorsOdd (row0829.map Prod.snd) oddDots0829 641 10 = true := by
  decide +kernel

theorem evenSum0830_checked :
    packedSumCheck packedFactorsEven (row0830.map Prod.fst) evenDots0830 641 10 = true := by
  decide +kernel

theorem oddSum0830_checked :
    packedSumCheck packedFactorsOdd (row0830.map Prod.snd) oddDots0830 641 10 = true := by
  decide +kernel

theorem evenSum0831_checked :
    packedSumCheck packedFactorsEven (row0831.map Prod.fst) evenDots0831 641 10 = true := by
  decide +kernel

theorem oddSum0831_checked :
    packedSumCheck packedFactorsOdd (row0831.map Prod.snd) oddDots0831 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
