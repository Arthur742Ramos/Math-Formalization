module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows101
public import ErdosOverlap.Certificate.Native6Grid.PackedDots101

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0808_checked :
    packedSumCheck packedFactorsEven (row0808.map Prod.fst) evenDots0808 641 10 = true := by
  decide +kernel

theorem oddSum0808_checked :
    packedSumCheck packedFactorsOdd (row0808.map Prod.snd) oddDots0808 641 10 = true := by
  decide +kernel

theorem evenSum0809_checked :
    packedSumCheck packedFactorsEven (row0809.map Prod.fst) evenDots0809 641 10 = true := by
  decide +kernel

theorem oddSum0809_checked :
    packedSumCheck packedFactorsOdd (row0809.map Prod.snd) oddDots0809 641 10 = true := by
  decide +kernel

theorem evenSum0810_checked :
    packedSumCheck packedFactorsEven (row0810.map Prod.fst) evenDots0810 641 10 = true := by
  decide +kernel

theorem oddSum0810_checked :
    packedSumCheck packedFactorsOdd (row0810.map Prod.snd) oddDots0810 641 10 = true := by
  decide +kernel

theorem evenSum0811_checked :
    packedSumCheck packedFactorsEven (row0811.map Prod.fst) evenDots0811 641 10 = true := by
  decide +kernel

theorem oddSum0811_checked :
    packedSumCheck packedFactorsOdd (row0811.map Prod.snd) oddDots0811 641 10 = true := by
  decide +kernel

theorem evenSum0812_checked :
    packedSumCheck packedFactorsEven (row0812.map Prod.fst) evenDots0812 641 10 = true := by
  decide +kernel

theorem oddSum0812_checked :
    packedSumCheck packedFactorsOdd (row0812.map Prod.snd) oddDots0812 641 10 = true := by
  decide +kernel

theorem evenSum0813_checked :
    packedSumCheck packedFactorsEven (row0813.map Prod.fst) evenDots0813 641 10 = true := by
  decide +kernel

theorem oddSum0813_checked :
    packedSumCheck packedFactorsOdd (row0813.map Prod.snd) oddDots0813 641 10 = true := by
  decide +kernel

theorem evenSum0814_checked :
    packedSumCheck packedFactorsEven (row0814.map Prod.fst) evenDots0814 641 10 = true := by
  decide +kernel

theorem oddSum0814_checked :
    packedSumCheck packedFactorsOdd (row0814.map Prod.snd) oddDots0814 641 10 = true := by
  decide +kernel

theorem evenSum0815_checked :
    packedSumCheck packedFactorsEven (row0815.map Prod.fst) evenDots0815 641 10 = true := by
  decide +kernel

theorem oddSum0815_checked :
    packedSumCheck packedFactorsOdd (row0815.map Prod.snd) oddDots0815 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
