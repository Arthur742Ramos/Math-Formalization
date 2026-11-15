module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows099
public import ErdosOverlap.Certificate.Native6Grid.PackedDots099

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0792_checked :
    packedSumCheck packedFactorsEven (row0792.map Prod.fst) evenDots0792 641 10 = true := by
  decide +kernel

theorem oddSum0792_checked :
    packedSumCheck packedFactorsOdd (row0792.map Prod.snd) oddDots0792 641 10 = true := by
  decide +kernel

theorem evenSum0793_checked :
    packedSumCheck packedFactorsEven (row0793.map Prod.fst) evenDots0793 641 10 = true := by
  decide +kernel

theorem oddSum0793_checked :
    packedSumCheck packedFactorsOdd (row0793.map Prod.snd) oddDots0793 641 10 = true := by
  decide +kernel

theorem evenSum0794_checked :
    packedSumCheck packedFactorsEven (row0794.map Prod.fst) evenDots0794 641 10 = true := by
  decide +kernel

theorem oddSum0794_checked :
    packedSumCheck packedFactorsOdd (row0794.map Prod.snd) oddDots0794 641 10 = true := by
  decide +kernel

theorem evenSum0795_checked :
    packedSumCheck packedFactorsEven (row0795.map Prod.fst) evenDots0795 641 10 = true := by
  decide +kernel

theorem oddSum0795_checked :
    packedSumCheck packedFactorsOdd (row0795.map Prod.snd) oddDots0795 641 10 = true := by
  decide +kernel

theorem evenSum0796_checked :
    packedSumCheck packedFactorsEven (row0796.map Prod.fst) evenDots0796 641 10 = true := by
  decide +kernel

theorem oddSum0796_checked :
    packedSumCheck packedFactorsOdd (row0796.map Prod.snd) oddDots0796 641 10 = true := by
  decide +kernel

theorem evenSum0797_checked :
    packedSumCheck packedFactorsEven (row0797.map Prod.fst) evenDots0797 641 10 = true := by
  decide +kernel

theorem oddSum0797_checked :
    packedSumCheck packedFactorsOdd (row0797.map Prod.snd) oddDots0797 641 10 = true := by
  decide +kernel

theorem evenSum0798_checked :
    packedSumCheck packedFactorsEven (row0798.map Prod.fst) evenDots0798 641 10 = true := by
  decide +kernel

theorem oddSum0798_checked :
    packedSumCheck packedFactorsOdd (row0798.map Prod.snd) oddDots0798 641 10 = true := by
  decide +kernel

theorem evenSum0799_checked :
    packedSumCheck packedFactorsEven (row0799.map Prod.fst) evenDots0799 641 10 = true := by
  decide +kernel

theorem oddSum0799_checked :
    packedSumCheck packedFactorsOdd (row0799.map Prod.snd) oddDots0799 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
