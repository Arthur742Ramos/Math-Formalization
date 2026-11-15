module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows041
public import ErdosOverlap.Certificate.Native6Grid.PackedDots041

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0328_checked :
    packedSumCheck packedFactorsEven (row0328.map Prod.fst) evenDots0328 641 10 = true := by
  decide +kernel

theorem oddSum0328_checked :
    packedSumCheck packedFactorsOdd (row0328.map Prod.snd) oddDots0328 641 10 = true := by
  decide +kernel

theorem evenSum0329_checked :
    packedSumCheck packedFactorsEven (row0329.map Prod.fst) evenDots0329 641 10 = true := by
  decide +kernel

theorem oddSum0329_checked :
    packedSumCheck packedFactorsOdd (row0329.map Prod.snd) oddDots0329 641 10 = true := by
  decide +kernel

theorem evenSum0330_checked :
    packedSumCheck packedFactorsEven (row0330.map Prod.fst) evenDots0330 641 10 = true := by
  decide +kernel

theorem oddSum0330_checked :
    packedSumCheck packedFactorsOdd (row0330.map Prod.snd) oddDots0330 641 10 = true := by
  decide +kernel

theorem evenSum0331_checked :
    packedSumCheck packedFactorsEven (row0331.map Prod.fst) evenDots0331 641 10 = true := by
  decide +kernel

theorem oddSum0331_checked :
    packedSumCheck packedFactorsOdd (row0331.map Prod.snd) oddDots0331 641 10 = true := by
  decide +kernel

theorem evenSum0332_checked :
    packedSumCheck packedFactorsEven (row0332.map Prod.fst) evenDots0332 641 10 = true := by
  decide +kernel

theorem oddSum0332_checked :
    packedSumCheck packedFactorsOdd (row0332.map Prod.snd) oddDots0332 641 10 = true := by
  decide +kernel

theorem evenSum0333_checked :
    packedSumCheck packedFactorsEven (row0333.map Prod.fst) evenDots0333 641 10 = true := by
  decide +kernel

theorem oddSum0333_checked :
    packedSumCheck packedFactorsOdd (row0333.map Prod.snd) oddDots0333 641 10 = true := by
  decide +kernel

theorem evenSum0334_checked :
    packedSumCheck packedFactorsEven (row0334.map Prod.fst) evenDots0334 641 10 = true := by
  decide +kernel

theorem oddSum0334_checked :
    packedSumCheck packedFactorsOdd (row0334.map Prod.snd) oddDots0334 641 10 = true := by
  decide +kernel

theorem evenSum0335_checked :
    packedSumCheck packedFactorsEven (row0335.map Prod.fst) evenDots0335 641 10 = true := by
  decide +kernel

theorem oddSum0335_checked :
    packedSumCheck packedFactorsOdd (row0335.map Prod.snd) oddDots0335 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
