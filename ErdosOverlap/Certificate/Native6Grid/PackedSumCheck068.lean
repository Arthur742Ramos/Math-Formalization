module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows068
public import ErdosOverlap.Certificate.Native6Grid.PackedDots068

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0544_checked :
    packedSumCheck packedFactorsEven (row0544.map Prod.fst) evenDots0544 641 10 = true := by
  decide +kernel

theorem oddSum0544_checked :
    packedSumCheck packedFactorsOdd (row0544.map Prod.snd) oddDots0544 641 10 = true := by
  decide +kernel

theorem evenSum0545_checked :
    packedSumCheck packedFactorsEven (row0545.map Prod.fst) evenDots0545 641 10 = true := by
  decide +kernel

theorem oddSum0545_checked :
    packedSumCheck packedFactorsOdd (row0545.map Prod.snd) oddDots0545 641 10 = true := by
  decide +kernel

theorem evenSum0546_checked :
    packedSumCheck packedFactorsEven (row0546.map Prod.fst) evenDots0546 641 10 = true := by
  decide +kernel

theorem oddSum0546_checked :
    packedSumCheck packedFactorsOdd (row0546.map Prod.snd) oddDots0546 641 10 = true := by
  decide +kernel

theorem evenSum0547_checked :
    packedSumCheck packedFactorsEven (row0547.map Prod.fst) evenDots0547 641 10 = true := by
  decide +kernel

theorem oddSum0547_checked :
    packedSumCheck packedFactorsOdd (row0547.map Prod.snd) oddDots0547 641 10 = true := by
  decide +kernel

theorem evenSum0548_checked :
    packedSumCheck packedFactorsEven (row0548.map Prod.fst) evenDots0548 641 10 = true := by
  decide +kernel

theorem oddSum0548_checked :
    packedSumCheck packedFactorsOdd (row0548.map Prod.snd) oddDots0548 641 10 = true := by
  decide +kernel

theorem evenSum0549_checked :
    packedSumCheck packedFactorsEven (row0549.map Prod.fst) evenDots0549 641 10 = true := by
  decide +kernel

theorem oddSum0549_checked :
    packedSumCheck packedFactorsOdd (row0549.map Prod.snd) oddDots0549 641 10 = true := by
  decide +kernel

theorem evenSum0550_checked :
    packedSumCheck packedFactorsEven (row0550.map Prod.fst) evenDots0550 641 10 = true := by
  decide +kernel

theorem oddSum0550_checked :
    packedSumCheck packedFactorsOdd (row0550.map Prod.snd) oddDots0550 641 10 = true := by
  decide +kernel

theorem evenSum0551_checked :
    packedSumCheck packedFactorsEven (row0551.map Prod.fst) evenDots0551 641 10 = true := by
  decide +kernel

theorem oddSum0551_checked :
    packedSumCheck packedFactorsOdd (row0551.map Prod.snd) oddDots0551 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
