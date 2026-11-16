module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows102
public import ErdosOverlap.Certificate.Native6Grid.PackedDots102

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0816_checked :
    packedSumCheck packedFactorsEven (row0816.map Prod.fst) evenDots0816 641 10 = true := by
  decide +kernel

theorem oddSum0816_checked :
    packedSumCheck packedFactorsOdd (row0816.map Prod.snd) oddDots0816 641 10 = true := by
  decide +kernel

theorem evenSum0817_checked :
    packedSumCheck packedFactorsEven (row0817.map Prod.fst) evenDots0817 641 10 = true := by
  decide +kernel

theorem oddSum0817_checked :
    packedSumCheck packedFactorsOdd (row0817.map Prod.snd) oddDots0817 641 10 = true := by
  decide +kernel

theorem evenSum0818_checked :
    packedSumCheck packedFactorsEven (row0818.map Prod.fst) evenDots0818 641 10 = true := by
  decide +kernel

theorem oddSum0818_checked :
    packedSumCheck packedFactorsOdd (row0818.map Prod.snd) oddDots0818 641 10 = true := by
  decide +kernel

theorem evenSum0819_checked :
    packedSumCheck packedFactorsEven (row0819.map Prod.fst) evenDots0819 641 10 = true := by
  decide +kernel

theorem oddSum0819_checked :
    packedSumCheck packedFactorsOdd (row0819.map Prod.snd) oddDots0819 641 10 = true := by
  decide +kernel

theorem evenSum0820_checked :
    packedSumCheck packedFactorsEven (row0820.map Prod.fst) evenDots0820 641 10 = true := by
  decide +kernel

theorem oddSum0820_checked :
    packedSumCheck packedFactorsOdd (row0820.map Prod.snd) oddDots0820 641 10 = true := by
  decide +kernel

theorem evenSum0821_checked :
    packedSumCheck packedFactorsEven (row0821.map Prod.fst) evenDots0821 641 10 = true := by
  decide +kernel

theorem oddSum0821_checked :
    packedSumCheck packedFactorsOdd (row0821.map Prod.snd) oddDots0821 641 10 = true := by
  decide +kernel

theorem evenSum0822_checked :
    packedSumCheck packedFactorsEven (row0822.map Prod.fst) evenDots0822 641 10 = true := by
  decide +kernel

theorem oddSum0822_checked :
    packedSumCheck packedFactorsOdd (row0822.map Prod.snd) oddDots0822 641 10 = true := by
  decide +kernel

theorem evenSum0823_checked :
    packedSumCheck packedFactorsEven (row0823.map Prod.fst) evenDots0823 641 10 = true := by
  decide +kernel

theorem oddSum0823_checked :
    packedSumCheck packedFactorsOdd (row0823.map Prod.snd) oddDots0823 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
