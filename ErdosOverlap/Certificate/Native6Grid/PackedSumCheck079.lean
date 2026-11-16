module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows079
public import ErdosOverlap.Certificate.Native6Grid.PackedDots079

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0632_checked :
    packedSumCheck packedFactorsEven (row0632.map Prod.fst) evenDots0632 641 10 = true := by
  decide +kernel

theorem oddSum0632_checked :
    packedSumCheck packedFactorsOdd (row0632.map Prod.snd) oddDots0632 641 10 = true := by
  decide +kernel

theorem evenSum0633_checked :
    packedSumCheck packedFactorsEven (row0633.map Prod.fst) evenDots0633 641 10 = true := by
  decide +kernel

theorem oddSum0633_checked :
    packedSumCheck packedFactorsOdd (row0633.map Prod.snd) oddDots0633 641 10 = true := by
  decide +kernel

theorem evenSum0634_checked :
    packedSumCheck packedFactorsEven (row0634.map Prod.fst) evenDots0634 641 10 = true := by
  decide +kernel

theorem oddSum0634_checked :
    packedSumCheck packedFactorsOdd (row0634.map Prod.snd) oddDots0634 641 10 = true := by
  decide +kernel

theorem evenSum0635_checked :
    packedSumCheck packedFactorsEven (row0635.map Prod.fst) evenDots0635 641 10 = true := by
  decide +kernel

theorem oddSum0635_checked :
    packedSumCheck packedFactorsOdd (row0635.map Prod.snd) oddDots0635 641 10 = true := by
  decide +kernel

theorem evenSum0636_checked :
    packedSumCheck packedFactorsEven (row0636.map Prod.fst) evenDots0636 641 10 = true := by
  decide +kernel

theorem oddSum0636_checked :
    packedSumCheck packedFactorsOdd (row0636.map Prod.snd) oddDots0636 641 10 = true := by
  decide +kernel

theorem evenSum0637_checked :
    packedSumCheck packedFactorsEven (row0637.map Prod.fst) evenDots0637 641 10 = true := by
  decide +kernel

theorem oddSum0637_checked :
    packedSumCheck packedFactorsOdd (row0637.map Prod.snd) oddDots0637 641 10 = true := by
  decide +kernel

theorem evenSum0638_checked :
    packedSumCheck packedFactorsEven (row0638.map Prod.fst) evenDots0638 641 10 = true := by
  decide +kernel

theorem oddSum0638_checked :
    packedSumCheck packedFactorsOdd (row0638.map Prod.snd) oddDots0638 641 10 = true := by
  decide +kernel

theorem evenSum0639_checked :
    packedSumCheck packedFactorsEven (row0639.map Prod.fst) evenDots0639 641 10 = true := by
  decide +kernel

theorem oddSum0639_checked :
    packedSumCheck packedFactorsOdd (row0639.map Prod.snd) oddDots0639 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
