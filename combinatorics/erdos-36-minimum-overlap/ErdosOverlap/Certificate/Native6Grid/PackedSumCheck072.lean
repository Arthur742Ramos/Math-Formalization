module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows072
public import ErdosOverlap.Certificate.Native6Grid.PackedDots072

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0576_checked :
    packedSumCheck packedFactorsEven (row0576.map Prod.fst) evenDots0576 641 10 = true := by
  decide +kernel

theorem oddSum0576_checked :
    packedSumCheck packedFactorsOdd (row0576.map Prod.snd) oddDots0576 641 10 = true := by
  decide +kernel

theorem evenSum0577_checked :
    packedSumCheck packedFactorsEven (row0577.map Prod.fst) evenDots0577 641 10 = true := by
  decide +kernel

theorem oddSum0577_checked :
    packedSumCheck packedFactorsOdd (row0577.map Prod.snd) oddDots0577 641 10 = true := by
  decide +kernel

theorem evenSum0578_checked :
    packedSumCheck packedFactorsEven (row0578.map Prod.fst) evenDots0578 641 10 = true := by
  decide +kernel

theorem oddSum0578_checked :
    packedSumCheck packedFactorsOdd (row0578.map Prod.snd) oddDots0578 641 10 = true := by
  decide +kernel

theorem evenSum0579_checked :
    packedSumCheck packedFactorsEven (row0579.map Prod.fst) evenDots0579 641 10 = true := by
  decide +kernel

theorem oddSum0579_checked :
    packedSumCheck packedFactorsOdd (row0579.map Prod.snd) oddDots0579 641 10 = true := by
  decide +kernel

theorem evenSum0580_checked :
    packedSumCheck packedFactorsEven (row0580.map Prod.fst) evenDots0580 641 10 = true := by
  decide +kernel

theorem oddSum0580_checked :
    packedSumCheck packedFactorsOdd (row0580.map Prod.snd) oddDots0580 641 10 = true := by
  decide +kernel

theorem evenSum0581_checked :
    packedSumCheck packedFactorsEven (row0581.map Prod.fst) evenDots0581 641 10 = true := by
  decide +kernel

theorem oddSum0581_checked :
    packedSumCheck packedFactorsOdd (row0581.map Prod.snd) oddDots0581 641 10 = true := by
  decide +kernel

theorem evenSum0582_checked :
    packedSumCheck packedFactorsEven (row0582.map Prod.fst) evenDots0582 641 10 = true := by
  decide +kernel

theorem oddSum0582_checked :
    packedSumCheck packedFactorsOdd (row0582.map Prod.snd) oddDots0582 641 10 = true := by
  decide +kernel

theorem evenSum0583_checked :
    packedSumCheck packedFactorsEven (row0583.map Prod.fst) evenDots0583 641 10 = true := by
  decide +kernel

theorem oddSum0583_checked :
    packedSumCheck packedFactorsOdd (row0583.map Prod.snd) oddDots0583 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
