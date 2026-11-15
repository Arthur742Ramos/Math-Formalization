module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows071
public import ErdosOverlap.Certificate.Native6Grid.PackedDots071

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0568_checked :
    packedSumCheck packedFactorsEven (row0568.map Prod.fst) evenDots0568 641 10 = true := by
  decide +kernel

theorem oddSum0568_checked :
    packedSumCheck packedFactorsOdd (row0568.map Prod.snd) oddDots0568 641 10 = true := by
  decide +kernel

theorem evenSum0569_checked :
    packedSumCheck packedFactorsEven (row0569.map Prod.fst) evenDots0569 641 10 = true := by
  decide +kernel

theorem oddSum0569_checked :
    packedSumCheck packedFactorsOdd (row0569.map Prod.snd) oddDots0569 641 10 = true := by
  decide +kernel

theorem evenSum0570_checked :
    packedSumCheck packedFactorsEven (row0570.map Prod.fst) evenDots0570 641 10 = true := by
  decide +kernel

theorem oddSum0570_checked :
    packedSumCheck packedFactorsOdd (row0570.map Prod.snd) oddDots0570 641 10 = true := by
  decide +kernel

theorem evenSum0571_checked :
    packedSumCheck packedFactorsEven (row0571.map Prod.fst) evenDots0571 641 10 = true := by
  decide +kernel

theorem oddSum0571_checked :
    packedSumCheck packedFactorsOdd (row0571.map Prod.snd) oddDots0571 641 10 = true := by
  decide +kernel

theorem evenSum0572_checked :
    packedSumCheck packedFactorsEven (row0572.map Prod.fst) evenDots0572 641 10 = true := by
  decide +kernel

theorem oddSum0572_checked :
    packedSumCheck packedFactorsOdd (row0572.map Prod.snd) oddDots0572 641 10 = true := by
  decide +kernel

theorem evenSum0573_checked :
    packedSumCheck packedFactorsEven (row0573.map Prod.fst) evenDots0573 641 10 = true := by
  decide +kernel

theorem oddSum0573_checked :
    packedSumCheck packedFactorsOdd (row0573.map Prod.snd) oddDots0573 641 10 = true := by
  decide +kernel

theorem evenSum0574_checked :
    packedSumCheck packedFactorsEven (row0574.map Prod.fst) evenDots0574 641 10 = true := by
  decide +kernel

theorem oddSum0574_checked :
    packedSumCheck packedFactorsOdd (row0574.map Prod.snd) oddDots0574 641 10 = true := by
  decide +kernel

theorem evenSum0575_checked :
    packedSumCheck packedFactorsEven (row0575.map Prod.fst) evenDots0575 641 10 = true := by
  decide +kernel

theorem oddSum0575_checked :
    packedSumCheck packedFactorsOdd (row0575.map Prod.snd) oddDots0575 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
