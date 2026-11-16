module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows076
public import ErdosOverlap.Certificate.Native6Grid.PackedDots076

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0608_checked :
    packedSumCheck packedFactorsEven (row0608.map Prod.fst) evenDots0608 641 10 = true := by
  decide +kernel

theorem oddSum0608_checked :
    packedSumCheck packedFactorsOdd (row0608.map Prod.snd) oddDots0608 641 10 = true := by
  decide +kernel

theorem evenSum0609_checked :
    packedSumCheck packedFactorsEven (row0609.map Prod.fst) evenDots0609 641 10 = true := by
  decide +kernel

theorem oddSum0609_checked :
    packedSumCheck packedFactorsOdd (row0609.map Prod.snd) oddDots0609 641 10 = true := by
  decide +kernel

theorem evenSum0610_checked :
    packedSumCheck packedFactorsEven (row0610.map Prod.fst) evenDots0610 641 10 = true := by
  decide +kernel

theorem oddSum0610_checked :
    packedSumCheck packedFactorsOdd (row0610.map Prod.snd) oddDots0610 641 10 = true := by
  decide +kernel

theorem evenSum0611_checked :
    packedSumCheck packedFactorsEven (row0611.map Prod.fst) evenDots0611 641 10 = true := by
  decide +kernel

theorem oddSum0611_checked :
    packedSumCheck packedFactorsOdd (row0611.map Prod.snd) oddDots0611 641 10 = true := by
  decide +kernel

theorem evenSum0612_checked :
    packedSumCheck packedFactorsEven (row0612.map Prod.fst) evenDots0612 641 10 = true := by
  decide +kernel

theorem oddSum0612_checked :
    packedSumCheck packedFactorsOdd (row0612.map Prod.snd) oddDots0612 641 10 = true := by
  decide +kernel

theorem evenSum0613_checked :
    packedSumCheck packedFactorsEven (row0613.map Prod.fst) evenDots0613 641 10 = true := by
  decide +kernel

theorem oddSum0613_checked :
    packedSumCheck packedFactorsOdd (row0613.map Prod.snd) oddDots0613 641 10 = true := by
  decide +kernel

theorem evenSum0614_checked :
    packedSumCheck packedFactorsEven (row0614.map Prod.fst) evenDots0614 641 10 = true := by
  decide +kernel

theorem oddSum0614_checked :
    packedSumCheck packedFactorsOdd (row0614.map Prod.snd) oddDots0614 641 10 = true := by
  decide +kernel

theorem evenSum0615_checked :
    packedSumCheck packedFactorsEven (row0615.map Prod.fst) evenDots0615 641 10 = true := by
  decide +kernel

theorem oddSum0615_checked :
    packedSumCheck packedFactorsOdd (row0615.map Prod.snd) oddDots0615 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
