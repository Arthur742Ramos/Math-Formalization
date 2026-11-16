module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows087
public import ErdosOverlap.Certificate.Native6Grid.PackedDots087

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0696_checked :
    packedSumCheck packedFactorsEven (row0696.map Prod.fst) evenDots0696 641 10 = true := by
  decide +kernel

theorem oddSum0696_checked :
    packedSumCheck packedFactorsOdd (row0696.map Prod.snd) oddDots0696 641 10 = true := by
  decide +kernel

theorem evenSum0697_checked :
    packedSumCheck packedFactorsEven (row0697.map Prod.fst) evenDots0697 641 10 = true := by
  decide +kernel

theorem oddSum0697_checked :
    packedSumCheck packedFactorsOdd (row0697.map Prod.snd) oddDots0697 641 10 = true := by
  decide +kernel

theorem evenSum0698_checked :
    packedSumCheck packedFactorsEven (row0698.map Prod.fst) evenDots0698 641 10 = true := by
  decide +kernel

theorem oddSum0698_checked :
    packedSumCheck packedFactorsOdd (row0698.map Prod.snd) oddDots0698 641 10 = true := by
  decide +kernel

theorem evenSum0699_checked :
    packedSumCheck packedFactorsEven (row0699.map Prod.fst) evenDots0699 641 10 = true := by
  decide +kernel

theorem oddSum0699_checked :
    packedSumCheck packedFactorsOdd (row0699.map Prod.snd) oddDots0699 641 10 = true := by
  decide +kernel

theorem evenSum0700_checked :
    packedSumCheck packedFactorsEven (row0700.map Prod.fst) evenDots0700 641 10 = true := by
  decide +kernel

theorem oddSum0700_checked :
    packedSumCheck packedFactorsOdd (row0700.map Prod.snd) oddDots0700 641 10 = true := by
  decide +kernel

theorem evenSum0701_checked :
    packedSumCheck packedFactorsEven (row0701.map Prod.fst) evenDots0701 641 10 = true := by
  decide +kernel

theorem oddSum0701_checked :
    packedSumCheck packedFactorsOdd (row0701.map Prod.snd) oddDots0701 641 10 = true := by
  decide +kernel

theorem evenSum0702_checked :
    packedSumCheck packedFactorsEven (row0702.map Prod.fst) evenDots0702 641 10 = true := by
  decide +kernel

theorem oddSum0702_checked :
    packedSumCheck packedFactorsOdd (row0702.map Prod.snd) oddDots0702 641 10 = true := by
  decide +kernel

theorem evenSum0703_checked :
    packedSumCheck packedFactorsEven (row0703.map Prod.fst) evenDots0703 641 10 = true := by
  decide +kernel

theorem oddSum0703_checked :
    packedSumCheck packedFactorsOdd (row0703.map Prod.snd) oddDots0703 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
