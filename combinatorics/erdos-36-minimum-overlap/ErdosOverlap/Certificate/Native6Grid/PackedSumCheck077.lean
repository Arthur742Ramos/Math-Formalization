module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows077
public import ErdosOverlap.Certificate.Native6Grid.PackedDots077

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0616_checked :
    packedSumCheck packedFactorsEven (row0616.map Prod.fst) evenDots0616 641 10 = true := by
  decide +kernel

theorem oddSum0616_checked :
    packedSumCheck packedFactorsOdd (row0616.map Prod.snd) oddDots0616 641 10 = true := by
  decide +kernel

theorem evenSum0617_checked :
    packedSumCheck packedFactorsEven (row0617.map Prod.fst) evenDots0617 641 10 = true := by
  decide +kernel

theorem oddSum0617_checked :
    packedSumCheck packedFactorsOdd (row0617.map Prod.snd) oddDots0617 641 10 = true := by
  decide +kernel

theorem evenSum0618_checked :
    packedSumCheck packedFactorsEven (row0618.map Prod.fst) evenDots0618 641 10 = true := by
  decide +kernel

theorem oddSum0618_checked :
    packedSumCheck packedFactorsOdd (row0618.map Prod.snd) oddDots0618 641 10 = true := by
  decide +kernel

theorem evenSum0619_checked :
    packedSumCheck packedFactorsEven (row0619.map Prod.fst) evenDots0619 641 10 = true := by
  decide +kernel

theorem oddSum0619_checked :
    packedSumCheck packedFactorsOdd (row0619.map Prod.snd) oddDots0619 641 10 = true := by
  decide +kernel

theorem evenSum0620_checked :
    packedSumCheck packedFactorsEven (row0620.map Prod.fst) evenDots0620 641 10 = true := by
  decide +kernel

theorem oddSum0620_checked :
    packedSumCheck packedFactorsOdd (row0620.map Prod.snd) oddDots0620 641 10 = true := by
  decide +kernel

theorem evenSum0621_checked :
    packedSumCheck packedFactorsEven (row0621.map Prod.fst) evenDots0621 641 10 = true := by
  decide +kernel

theorem oddSum0621_checked :
    packedSumCheck packedFactorsOdd (row0621.map Prod.snd) oddDots0621 641 10 = true := by
  decide +kernel

theorem evenSum0622_checked :
    packedSumCheck packedFactorsEven (row0622.map Prod.fst) evenDots0622 641 10 = true := by
  decide +kernel

theorem oddSum0622_checked :
    packedSumCheck packedFactorsOdd (row0622.map Prod.snd) oddDots0622 641 10 = true := by
  decide +kernel

theorem evenSum0623_checked :
    packedSumCheck packedFactorsEven (row0623.map Prod.fst) evenDots0623 641 10 = true := by
  decide +kernel

theorem oddSum0623_checked :
    packedSumCheck packedFactorsOdd (row0623.map Prod.snd) oddDots0623 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
