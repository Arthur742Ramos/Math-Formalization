module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows096
public import ErdosOverlap.Certificate.Native6Grid.PackedDots096

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0768_checked :
    packedSumCheck packedFactorsEven (row0768.map Prod.fst) evenDots0768 641 10 = true := by
  decide +kernel

theorem oddSum0768_checked :
    packedSumCheck packedFactorsOdd (row0768.map Prod.snd) oddDots0768 641 10 = true := by
  decide +kernel

theorem evenSum0769_checked :
    packedSumCheck packedFactorsEven (row0769.map Prod.fst) evenDots0769 641 10 = true := by
  decide +kernel

theorem oddSum0769_checked :
    packedSumCheck packedFactorsOdd (row0769.map Prod.snd) oddDots0769 641 10 = true := by
  decide +kernel

theorem evenSum0770_checked :
    packedSumCheck packedFactorsEven (row0770.map Prod.fst) evenDots0770 641 10 = true := by
  decide +kernel

theorem oddSum0770_checked :
    packedSumCheck packedFactorsOdd (row0770.map Prod.snd) oddDots0770 641 10 = true := by
  decide +kernel

theorem evenSum0771_checked :
    packedSumCheck packedFactorsEven (row0771.map Prod.fst) evenDots0771 641 10 = true := by
  decide +kernel

theorem oddSum0771_checked :
    packedSumCheck packedFactorsOdd (row0771.map Prod.snd) oddDots0771 641 10 = true := by
  decide +kernel

theorem evenSum0772_checked :
    packedSumCheck packedFactorsEven (row0772.map Prod.fst) evenDots0772 641 10 = true := by
  decide +kernel

theorem oddSum0772_checked :
    packedSumCheck packedFactorsOdd (row0772.map Prod.snd) oddDots0772 641 10 = true := by
  decide +kernel

theorem evenSum0773_checked :
    packedSumCheck packedFactorsEven (row0773.map Prod.fst) evenDots0773 641 10 = true := by
  decide +kernel

theorem oddSum0773_checked :
    packedSumCheck packedFactorsOdd (row0773.map Prod.snd) oddDots0773 641 10 = true := by
  decide +kernel

theorem evenSum0774_checked :
    packedSumCheck packedFactorsEven (row0774.map Prod.fst) evenDots0774 641 10 = true := by
  decide +kernel

theorem oddSum0774_checked :
    packedSumCheck packedFactorsOdd (row0774.map Prod.snd) oddDots0774 641 10 = true := by
  decide +kernel

theorem evenSum0775_checked :
    packedSumCheck packedFactorsEven (row0775.map Prod.fst) evenDots0775 641 10 = true := by
  decide +kernel

theorem oddSum0775_checked :
    packedSumCheck packedFactorsOdd (row0775.map Prod.snd) oddDots0775 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
