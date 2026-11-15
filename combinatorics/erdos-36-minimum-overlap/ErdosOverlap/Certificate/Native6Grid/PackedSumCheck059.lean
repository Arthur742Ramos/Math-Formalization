module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows059
public import ErdosOverlap.Certificate.Native6Grid.PackedDots059

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0472_checked :
    packedSumCheck packedFactorsEven (row0472.map Prod.fst) evenDots0472 641 10 = true := by
  decide +kernel

theorem oddSum0472_checked :
    packedSumCheck packedFactorsOdd (row0472.map Prod.snd) oddDots0472 641 10 = true := by
  decide +kernel

theorem evenSum0473_checked :
    packedSumCheck packedFactorsEven (row0473.map Prod.fst) evenDots0473 641 10 = true := by
  decide +kernel

theorem oddSum0473_checked :
    packedSumCheck packedFactorsOdd (row0473.map Prod.snd) oddDots0473 641 10 = true := by
  decide +kernel

theorem evenSum0474_checked :
    packedSumCheck packedFactorsEven (row0474.map Prod.fst) evenDots0474 641 10 = true := by
  decide +kernel

theorem oddSum0474_checked :
    packedSumCheck packedFactorsOdd (row0474.map Prod.snd) oddDots0474 641 10 = true := by
  decide +kernel

theorem evenSum0475_checked :
    packedSumCheck packedFactorsEven (row0475.map Prod.fst) evenDots0475 641 10 = true := by
  decide +kernel

theorem oddSum0475_checked :
    packedSumCheck packedFactorsOdd (row0475.map Prod.snd) oddDots0475 641 10 = true := by
  decide +kernel

theorem evenSum0476_checked :
    packedSumCheck packedFactorsEven (row0476.map Prod.fst) evenDots0476 641 10 = true := by
  decide +kernel

theorem oddSum0476_checked :
    packedSumCheck packedFactorsOdd (row0476.map Prod.snd) oddDots0476 641 10 = true := by
  decide +kernel

theorem evenSum0477_checked :
    packedSumCheck packedFactorsEven (row0477.map Prod.fst) evenDots0477 641 10 = true := by
  decide +kernel

theorem oddSum0477_checked :
    packedSumCheck packedFactorsOdd (row0477.map Prod.snd) oddDots0477 641 10 = true := by
  decide +kernel

theorem evenSum0478_checked :
    packedSumCheck packedFactorsEven (row0478.map Prod.fst) evenDots0478 641 10 = true := by
  decide +kernel

theorem oddSum0478_checked :
    packedSumCheck packedFactorsOdd (row0478.map Prod.snd) oddDots0478 641 10 = true := by
  decide +kernel

theorem evenSum0479_checked :
    packedSumCheck packedFactorsEven (row0479.map Prod.fst) evenDots0479 641 10 = true := by
  decide +kernel

theorem oddSum0479_checked :
    packedSumCheck packedFactorsOdd (row0479.map Prod.snd) oddDots0479 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
