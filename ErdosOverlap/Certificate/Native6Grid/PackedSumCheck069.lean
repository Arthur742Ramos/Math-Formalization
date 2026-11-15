module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows069
public import ErdosOverlap.Certificate.Native6Grid.PackedDots069

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0552_checked :
    packedSumCheck packedFactorsEven (row0552.map Prod.fst) evenDots0552 641 10 = true := by
  decide +kernel

theorem oddSum0552_checked :
    packedSumCheck packedFactorsOdd (row0552.map Prod.snd) oddDots0552 641 10 = true := by
  decide +kernel

theorem evenSum0553_checked :
    packedSumCheck packedFactorsEven (row0553.map Prod.fst) evenDots0553 641 10 = true := by
  decide +kernel

theorem oddSum0553_checked :
    packedSumCheck packedFactorsOdd (row0553.map Prod.snd) oddDots0553 641 10 = true := by
  decide +kernel

theorem evenSum0554_checked :
    packedSumCheck packedFactorsEven (row0554.map Prod.fst) evenDots0554 641 10 = true := by
  decide +kernel

theorem oddSum0554_checked :
    packedSumCheck packedFactorsOdd (row0554.map Prod.snd) oddDots0554 641 10 = true := by
  decide +kernel

theorem evenSum0555_checked :
    packedSumCheck packedFactorsEven (row0555.map Prod.fst) evenDots0555 641 10 = true := by
  decide +kernel

theorem oddSum0555_checked :
    packedSumCheck packedFactorsOdd (row0555.map Prod.snd) oddDots0555 641 10 = true := by
  decide +kernel

theorem evenSum0556_checked :
    packedSumCheck packedFactorsEven (row0556.map Prod.fst) evenDots0556 641 10 = true := by
  decide +kernel

theorem oddSum0556_checked :
    packedSumCheck packedFactorsOdd (row0556.map Prod.snd) oddDots0556 641 10 = true := by
  decide +kernel

theorem evenSum0557_checked :
    packedSumCheck packedFactorsEven (row0557.map Prod.fst) evenDots0557 641 10 = true := by
  decide +kernel

theorem oddSum0557_checked :
    packedSumCheck packedFactorsOdd (row0557.map Prod.snd) oddDots0557 641 10 = true := by
  decide +kernel

theorem evenSum0558_checked :
    packedSumCheck packedFactorsEven (row0558.map Prod.fst) evenDots0558 641 10 = true := by
  decide +kernel

theorem oddSum0558_checked :
    packedSumCheck packedFactorsOdd (row0558.map Prod.snd) oddDots0558 641 10 = true := by
  decide +kernel

theorem evenSum0559_checked :
    packedSumCheck packedFactorsEven (row0559.map Prod.fst) evenDots0559 641 10 = true := by
  decide +kernel

theorem oddSum0559_checked :
    packedSumCheck packedFactorsOdd (row0559.map Prod.snd) oddDots0559 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
