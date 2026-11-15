module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows080
public import ErdosOverlap.Certificate.Native6Grid.PackedDots080

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0640_checked :
    packedSumCheck packedFactorsEven (row0640.map Prod.fst) evenDots0640 641 10 = true := by
  decide +kernel

theorem oddSum0640_checked :
    packedSumCheck packedFactorsOdd (row0640.map Prod.snd) oddDots0640 641 10 = true := by
  decide +kernel

theorem evenSum0641_checked :
    packedSumCheck packedFactorsEven (row0641.map Prod.fst) evenDots0641 641 10 = true := by
  decide +kernel

theorem oddSum0641_checked :
    packedSumCheck packedFactorsOdd (row0641.map Prod.snd) oddDots0641 641 10 = true := by
  decide +kernel

theorem evenSum0642_checked :
    packedSumCheck packedFactorsEven (row0642.map Prod.fst) evenDots0642 641 10 = true := by
  decide +kernel

theorem oddSum0642_checked :
    packedSumCheck packedFactorsOdd (row0642.map Prod.snd) oddDots0642 641 10 = true := by
  decide +kernel

theorem evenSum0643_checked :
    packedSumCheck packedFactorsEven (row0643.map Prod.fst) evenDots0643 641 10 = true := by
  decide +kernel

theorem oddSum0643_checked :
    packedSumCheck packedFactorsOdd (row0643.map Prod.snd) oddDots0643 641 10 = true := by
  decide +kernel

theorem evenSum0644_checked :
    packedSumCheck packedFactorsEven (row0644.map Prod.fst) evenDots0644 641 10 = true := by
  decide +kernel

theorem oddSum0644_checked :
    packedSumCheck packedFactorsOdd (row0644.map Prod.snd) oddDots0644 641 10 = true := by
  decide +kernel

theorem evenSum0645_checked :
    packedSumCheck packedFactorsEven (row0645.map Prod.fst) evenDots0645 641 10 = true := by
  decide +kernel

theorem oddSum0645_checked :
    packedSumCheck packedFactorsOdd (row0645.map Prod.snd) oddDots0645 641 10 = true := by
  decide +kernel

theorem evenSum0646_checked :
    packedSumCheck packedFactorsEven (row0646.map Prod.fst) evenDots0646 641 10 = true := by
  decide +kernel

theorem oddSum0646_checked :
    packedSumCheck packedFactorsOdd (row0646.map Prod.snd) oddDots0646 641 10 = true := by
  decide +kernel

theorem evenSum0647_checked :
    packedSumCheck packedFactorsEven (row0647.map Prod.fst) evenDots0647 641 10 = true := by
  decide +kernel

theorem oddSum0647_checked :
    packedSumCheck packedFactorsOdd (row0647.map Prod.snd) oddDots0647 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
