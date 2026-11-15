module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows107
public import ErdosOverlap.Certificate.Native6Grid.PackedDots107

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0856_checked :
    packedSumCheck packedFactorsEven (row0856.map Prod.fst) evenDots0856 641 10 = true := by
  decide +kernel

theorem oddSum0856_checked :
    packedSumCheck packedFactorsOdd (row0856.map Prod.snd) oddDots0856 641 10 = true := by
  decide +kernel

theorem evenSum0857_checked :
    packedSumCheck packedFactorsEven (row0857.map Prod.fst) evenDots0857 641 10 = true := by
  decide +kernel

theorem oddSum0857_checked :
    packedSumCheck packedFactorsOdd (row0857.map Prod.snd) oddDots0857 641 10 = true := by
  decide +kernel

theorem evenSum0858_checked :
    packedSumCheck packedFactorsEven (row0858.map Prod.fst) evenDots0858 641 10 = true := by
  decide +kernel

theorem oddSum0858_checked :
    packedSumCheck packedFactorsOdd (row0858.map Prod.snd) oddDots0858 641 10 = true := by
  decide +kernel

theorem evenSum0859_checked :
    packedSumCheck packedFactorsEven (row0859.map Prod.fst) evenDots0859 641 10 = true := by
  decide +kernel

theorem oddSum0859_checked :
    packedSumCheck packedFactorsOdd (row0859.map Prod.snd) oddDots0859 641 10 = true := by
  decide +kernel

theorem evenSum0860_checked :
    packedSumCheck packedFactorsEven (row0860.map Prod.fst) evenDots0860 641 10 = true := by
  decide +kernel

theorem oddSum0860_checked :
    packedSumCheck packedFactorsOdd (row0860.map Prod.snd) oddDots0860 641 10 = true := by
  decide +kernel

theorem evenSum0861_checked :
    packedSumCheck packedFactorsEven (row0861.map Prod.fst) evenDots0861 641 10 = true := by
  decide +kernel

theorem oddSum0861_checked :
    packedSumCheck packedFactorsOdd (row0861.map Prod.snd) oddDots0861 641 10 = true := by
  decide +kernel

theorem evenSum0862_checked :
    packedSumCheck packedFactorsEven (row0862.map Prod.fst) evenDots0862 641 10 = true := by
  decide +kernel

theorem oddSum0862_checked :
    packedSumCheck packedFactorsOdd (row0862.map Prod.snd) oddDots0862 641 10 = true := by
  decide +kernel

theorem evenSum0863_checked :
    packedSumCheck packedFactorsEven (row0863.map Prod.fst) evenDots0863 641 10 = true := by
  decide +kernel

theorem oddSum0863_checked :
    packedSumCheck packedFactorsOdd (row0863.map Prod.snd) oddDots0863 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
