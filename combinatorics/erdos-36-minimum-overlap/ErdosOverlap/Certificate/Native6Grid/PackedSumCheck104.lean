module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows104
public import ErdosOverlap.Certificate.Native6Grid.PackedDots104

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0832_checked :
    packedSumCheck packedFactorsEven (row0832.map Prod.fst) evenDots0832 641 10 = true := by
  decide +kernel

theorem oddSum0832_checked :
    packedSumCheck packedFactorsOdd (row0832.map Prod.snd) oddDots0832 641 10 = true := by
  decide +kernel

theorem evenSum0833_checked :
    packedSumCheck packedFactorsEven (row0833.map Prod.fst) evenDots0833 641 10 = true := by
  decide +kernel

theorem oddSum0833_checked :
    packedSumCheck packedFactorsOdd (row0833.map Prod.snd) oddDots0833 641 10 = true := by
  decide +kernel

theorem evenSum0834_checked :
    packedSumCheck packedFactorsEven (row0834.map Prod.fst) evenDots0834 641 10 = true := by
  decide +kernel

theorem oddSum0834_checked :
    packedSumCheck packedFactorsOdd (row0834.map Prod.snd) oddDots0834 641 10 = true := by
  decide +kernel

theorem evenSum0835_checked :
    packedSumCheck packedFactorsEven (row0835.map Prod.fst) evenDots0835 641 10 = true := by
  decide +kernel

theorem oddSum0835_checked :
    packedSumCheck packedFactorsOdd (row0835.map Prod.snd) oddDots0835 641 10 = true := by
  decide +kernel

theorem evenSum0836_checked :
    packedSumCheck packedFactorsEven (row0836.map Prod.fst) evenDots0836 641 10 = true := by
  decide +kernel

theorem oddSum0836_checked :
    packedSumCheck packedFactorsOdd (row0836.map Prod.snd) oddDots0836 641 10 = true := by
  decide +kernel

theorem evenSum0837_checked :
    packedSumCheck packedFactorsEven (row0837.map Prod.fst) evenDots0837 641 10 = true := by
  decide +kernel

theorem oddSum0837_checked :
    packedSumCheck packedFactorsOdd (row0837.map Prod.snd) oddDots0837 641 10 = true := by
  decide +kernel

theorem evenSum0838_checked :
    packedSumCheck packedFactorsEven (row0838.map Prod.fst) evenDots0838 641 10 = true := by
  decide +kernel

theorem oddSum0838_checked :
    packedSumCheck packedFactorsOdd (row0838.map Prod.snd) oddDots0838 641 10 = true := by
  decide +kernel

theorem evenSum0839_checked :
    packedSumCheck packedFactorsEven (row0839.map Prod.fst) evenDots0839 641 10 = true := by
  decide +kernel

theorem oddSum0839_checked :
    packedSumCheck packedFactorsOdd (row0839.map Prod.snd) oddDots0839 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
