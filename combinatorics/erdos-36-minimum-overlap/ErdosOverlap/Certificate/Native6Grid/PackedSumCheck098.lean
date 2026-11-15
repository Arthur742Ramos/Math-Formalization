module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows098
public import ErdosOverlap.Certificate.Native6Grid.PackedDots098

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0784_checked :
    packedSumCheck packedFactorsEven (row0784.map Prod.fst) evenDots0784 641 10 = true := by
  decide +kernel

theorem oddSum0784_checked :
    packedSumCheck packedFactorsOdd (row0784.map Prod.snd) oddDots0784 641 10 = true := by
  decide +kernel

theorem evenSum0785_checked :
    packedSumCheck packedFactorsEven (row0785.map Prod.fst) evenDots0785 641 10 = true := by
  decide +kernel

theorem oddSum0785_checked :
    packedSumCheck packedFactorsOdd (row0785.map Prod.snd) oddDots0785 641 10 = true := by
  decide +kernel

theorem evenSum0786_checked :
    packedSumCheck packedFactorsEven (row0786.map Prod.fst) evenDots0786 641 10 = true := by
  decide +kernel

theorem oddSum0786_checked :
    packedSumCheck packedFactorsOdd (row0786.map Prod.snd) oddDots0786 641 10 = true := by
  decide +kernel

theorem evenSum0787_checked :
    packedSumCheck packedFactorsEven (row0787.map Prod.fst) evenDots0787 641 10 = true := by
  decide +kernel

theorem oddSum0787_checked :
    packedSumCheck packedFactorsOdd (row0787.map Prod.snd) oddDots0787 641 10 = true := by
  decide +kernel

theorem evenSum0788_checked :
    packedSumCheck packedFactorsEven (row0788.map Prod.fst) evenDots0788 641 10 = true := by
  decide +kernel

theorem oddSum0788_checked :
    packedSumCheck packedFactorsOdd (row0788.map Prod.snd) oddDots0788 641 10 = true := by
  decide +kernel

theorem evenSum0789_checked :
    packedSumCheck packedFactorsEven (row0789.map Prod.fst) evenDots0789 641 10 = true := by
  decide +kernel

theorem oddSum0789_checked :
    packedSumCheck packedFactorsOdd (row0789.map Prod.snd) oddDots0789 641 10 = true := by
  decide +kernel

theorem evenSum0790_checked :
    packedSumCheck packedFactorsEven (row0790.map Prod.fst) evenDots0790 641 10 = true := by
  decide +kernel

theorem oddSum0790_checked :
    packedSumCheck packedFactorsOdd (row0790.map Prod.snd) oddDots0790 641 10 = true := by
  decide +kernel

theorem evenSum0791_checked :
    packedSumCheck packedFactorsEven (row0791.map Prod.fst) evenDots0791 641 10 = true := by
  decide +kernel

theorem oddSum0791_checked :
    packedSumCheck packedFactorsOdd (row0791.map Prod.snd) oddDots0791 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
