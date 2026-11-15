module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows094
public import ErdosOverlap.Certificate.Native6Grid.PackedDots094

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0752_checked :
    packedSumCheck packedFactorsEven (row0752.map Prod.fst) evenDots0752 641 10 = true := by
  decide +kernel

theorem oddSum0752_checked :
    packedSumCheck packedFactorsOdd (row0752.map Prod.snd) oddDots0752 641 10 = true := by
  decide +kernel

theorem evenSum0753_checked :
    packedSumCheck packedFactorsEven (row0753.map Prod.fst) evenDots0753 641 10 = true := by
  decide +kernel

theorem oddSum0753_checked :
    packedSumCheck packedFactorsOdd (row0753.map Prod.snd) oddDots0753 641 10 = true := by
  decide +kernel

theorem evenSum0754_checked :
    packedSumCheck packedFactorsEven (row0754.map Prod.fst) evenDots0754 641 10 = true := by
  decide +kernel

theorem oddSum0754_checked :
    packedSumCheck packedFactorsOdd (row0754.map Prod.snd) oddDots0754 641 10 = true := by
  decide +kernel

theorem evenSum0755_checked :
    packedSumCheck packedFactorsEven (row0755.map Prod.fst) evenDots0755 641 10 = true := by
  decide +kernel

theorem oddSum0755_checked :
    packedSumCheck packedFactorsOdd (row0755.map Prod.snd) oddDots0755 641 10 = true := by
  decide +kernel

theorem evenSum0756_checked :
    packedSumCheck packedFactorsEven (row0756.map Prod.fst) evenDots0756 641 10 = true := by
  decide +kernel

theorem oddSum0756_checked :
    packedSumCheck packedFactorsOdd (row0756.map Prod.snd) oddDots0756 641 10 = true := by
  decide +kernel

theorem evenSum0757_checked :
    packedSumCheck packedFactorsEven (row0757.map Prod.fst) evenDots0757 641 10 = true := by
  decide +kernel

theorem oddSum0757_checked :
    packedSumCheck packedFactorsOdd (row0757.map Prod.snd) oddDots0757 641 10 = true := by
  decide +kernel

theorem evenSum0758_checked :
    packedSumCheck packedFactorsEven (row0758.map Prod.fst) evenDots0758 641 10 = true := by
  decide +kernel

theorem oddSum0758_checked :
    packedSumCheck packedFactorsOdd (row0758.map Prod.snd) oddDots0758 641 10 = true := by
  decide +kernel

theorem evenSum0759_checked :
    packedSumCheck packedFactorsEven (row0759.map Prod.fst) evenDots0759 641 10 = true := by
  decide +kernel

theorem oddSum0759_checked :
    packedSumCheck packedFactorsOdd (row0759.map Prod.snd) oddDots0759 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
