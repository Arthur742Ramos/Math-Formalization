module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows007
public import ErdosOverlap.Certificate.Native6Grid.PackedDots007

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0056_checked :
    packedSumCheck packedFactorsEven (row0056.map Prod.fst) evenDots0056 641 10 = true := by
  decide +kernel

theorem oddSum0056_checked :
    packedSumCheck packedFactorsOdd (row0056.map Prod.snd) oddDots0056 641 10 = true := by
  decide +kernel

theorem evenSum0057_checked :
    packedSumCheck packedFactorsEven (row0057.map Prod.fst) evenDots0057 641 10 = true := by
  decide +kernel

theorem oddSum0057_checked :
    packedSumCheck packedFactorsOdd (row0057.map Prod.snd) oddDots0057 641 10 = true := by
  decide +kernel

theorem evenSum0058_checked :
    packedSumCheck packedFactorsEven (row0058.map Prod.fst) evenDots0058 641 10 = true := by
  decide +kernel

theorem oddSum0058_checked :
    packedSumCheck packedFactorsOdd (row0058.map Prod.snd) oddDots0058 641 10 = true := by
  decide +kernel

theorem evenSum0059_checked :
    packedSumCheck packedFactorsEven (row0059.map Prod.fst) evenDots0059 641 10 = true := by
  decide +kernel

theorem oddSum0059_checked :
    packedSumCheck packedFactorsOdd (row0059.map Prod.snd) oddDots0059 641 10 = true := by
  decide +kernel

theorem evenSum0060_checked :
    packedSumCheck packedFactorsEven (row0060.map Prod.fst) evenDots0060 641 10 = true := by
  decide +kernel

theorem oddSum0060_checked :
    packedSumCheck packedFactorsOdd (row0060.map Prod.snd) oddDots0060 641 10 = true := by
  decide +kernel

theorem evenSum0061_checked :
    packedSumCheck packedFactorsEven (row0061.map Prod.fst) evenDots0061 641 10 = true := by
  decide +kernel

theorem oddSum0061_checked :
    packedSumCheck packedFactorsOdd (row0061.map Prod.snd) oddDots0061 641 10 = true := by
  decide +kernel

theorem evenSum0062_checked :
    packedSumCheck packedFactorsEven (row0062.map Prod.fst) evenDots0062 641 10 = true := by
  decide +kernel

theorem oddSum0062_checked :
    packedSumCheck packedFactorsOdd (row0062.map Prod.snd) oddDots0062 641 10 = true := by
  decide +kernel

theorem evenSum0063_checked :
    packedSumCheck packedFactorsEven (row0063.map Prod.fst) evenDots0063 641 10 = true := by
  decide +kernel

theorem oddSum0063_checked :
    packedSumCheck packedFactorsOdd (row0063.map Prod.snd) oddDots0063 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
