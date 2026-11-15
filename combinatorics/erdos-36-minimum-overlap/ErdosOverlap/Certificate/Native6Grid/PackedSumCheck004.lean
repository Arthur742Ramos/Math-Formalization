module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows004
public import ErdosOverlap.Certificate.Native6Grid.PackedDots004

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0032_checked :
    packedSumCheck packedFactorsEven (row0032.map Prod.fst) evenDots0032 641 10 = true := by
  decide +kernel

theorem oddSum0032_checked :
    packedSumCheck packedFactorsOdd (row0032.map Prod.snd) oddDots0032 641 10 = true := by
  decide +kernel

theorem evenSum0033_checked :
    packedSumCheck packedFactorsEven (row0033.map Prod.fst) evenDots0033 641 10 = true := by
  decide +kernel

theorem oddSum0033_checked :
    packedSumCheck packedFactorsOdd (row0033.map Prod.snd) oddDots0033 641 10 = true := by
  decide +kernel

theorem evenSum0034_checked :
    packedSumCheck packedFactorsEven (row0034.map Prod.fst) evenDots0034 641 10 = true := by
  decide +kernel

theorem oddSum0034_checked :
    packedSumCheck packedFactorsOdd (row0034.map Prod.snd) oddDots0034 641 10 = true := by
  decide +kernel

theorem evenSum0035_checked :
    packedSumCheck packedFactorsEven (row0035.map Prod.fst) evenDots0035 641 10 = true := by
  decide +kernel

theorem oddSum0035_checked :
    packedSumCheck packedFactorsOdd (row0035.map Prod.snd) oddDots0035 641 10 = true := by
  decide +kernel

theorem evenSum0036_checked :
    packedSumCheck packedFactorsEven (row0036.map Prod.fst) evenDots0036 641 10 = true := by
  decide +kernel

theorem oddSum0036_checked :
    packedSumCheck packedFactorsOdd (row0036.map Prod.snd) oddDots0036 641 10 = true := by
  decide +kernel

theorem evenSum0037_checked :
    packedSumCheck packedFactorsEven (row0037.map Prod.fst) evenDots0037 641 10 = true := by
  decide +kernel

theorem oddSum0037_checked :
    packedSumCheck packedFactorsOdd (row0037.map Prod.snd) oddDots0037 641 10 = true := by
  decide +kernel

theorem evenSum0038_checked :
    packedSumCheck packedFactorsEven (row0038.map Prod.fst) evenDots0038 641 10 = true := by
  decide +kernel

theorem oddSum0038_checked :
    packedSumCheck packedFactorsOdd (row0038.map Prod.snd) oddDots0038 641 10 = true := by
  decide +kernel

theorem evenSum0039_checked :
    packedSumCheck packedFactorsEven (row0039.map Prod.fst) evenDots0039 641 10 = true := by
  decide +kernel

theorem oddSum0039_checked :
    packedSumCheck packedFactorsOdd (row0039.map Prod.snd) oddDots0039 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
