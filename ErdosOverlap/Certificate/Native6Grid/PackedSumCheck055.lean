module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows055
public import ErdosOverlap.Certificate.Native6Grid.PackedDots055

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0440_checked :
    packedSumCheck packedFactorsEven (row0440.map Prod.fst) evenDots0440 641 10 = true := by
  decide +kernel

theorem oddSum0440_checked :
    packedSumCheck packedFactorsOdd (row0440.map Prod.snd) oddDots0440 641 10 = true := by
  decide +kernel

theorem evenSum0441_checked :
    packedSumCheck packedFactorsEven (row0441.map Prod.fst) evenDots0441 641 10 = true := by
  decide +kernel

theorem oddSum0441_checked :
    packedSumCheck packedFactorsOdd (row0441.map Prod.snd) oddDots0441 641 10 = true := by
  decide +kernel

theorem evenSum0442_checked :
    packedSumCheck packedFactorsEven (row0442.map Prod.fst) evenDots0442 641 10 = true := by
  decide +kernel

theorem oddSum0442_checked :
    packedSumCheck packedFactorsOdd (row0442.map Prod.snd) oddDots0442 641 10 = true := by
  decide +kernel

theorem evenSum0443_checked :
    packedSumCheck packedFactorsEven (row0443.map Prod.fst) evenDots0443 641 10 = true := by
  decide +kernel

theorem oddSum0443_checked :
    packedSumCheck packedFactorsOdd (row0443.map Prod.snd) oddDots0443 641 10 = true := by
  decide +kernel

theorem evenSum0444_checked :
    packedSumCheck packedFactorsEven (row0444.map Prod.fst) evenDots0444 641 10 = true := by
  decide +kernel

theorem oddSum0444_checked :
    packedSumCheck packedFactorsOdd (row0444.map Prod.snd) oddDots0444 641 10 = true := by
  decide +kernel

theorem evenSum0445_checked :
    packedSumCheck packedFactorsEven (row0445.map Prod.fst) evenDots0445 641 10 = true := by
  decide +kernel

theorem oddSum0445_checked :
    packedSumCheck packedFactorsOdd (row0445.map Prod.snd) oddDots0445 641 10 = true := by
  decide +kernel

theorem evenSum0446_checked :
    packedSumCheck packedFactorsEven (row0446.map Prod.fst) evenDots0446 641 10 = true := by
  decide +kernel

theorem oddSum0446_checked :
    packedSumCheck packedFactorsOdd (row0446.map Prod.snd) oddDots0446 641 10 = true := by
  decide +kernel

theorem evenSum0447_checked :
    packedSumCheck packedFactorsEven (row0447.map Prod.fst) evenDots0447 641 10 = true := by
  decide +kernel

theorem oddSum0447_checked :
    packedSumCheck packedFactorsOdd (row0447.map Prod.snd) oddDots0447 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
