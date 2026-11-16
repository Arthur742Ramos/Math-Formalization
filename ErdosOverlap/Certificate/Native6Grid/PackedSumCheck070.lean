module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows070
public import ErdosOverlap.Certificate.Native6Grid.PackedDots070

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0560_checked :
    packedSumCheck packedFactorsEven (row0560.map Prod.fst) evenDots0560 641 10 = true := by
  decide +kernel

theorem oddSum0560_checked :
    packedSumCheck packedFactorsOdd (row0560.map Prod.snd) oddDots0560 641 10 = true := by
  decide +kernel

theorem evenSum0561_checked :
    packedSumCheck packedFactorsEven (row0561.map Prod.fst) evenDots0561 641 10 = true := by
  decide +kernel

theorem oddSum0561_checked :
    packedSumCheck packedFactorsOdd (row0561.map Prod.snd) oddDots0561 641 10 = true := by
  decide +kernel

theorem evenSum0562_checked :
    packedSumCheck packedFactorsEven (row0562.map Prod.fst) evenDots0562 641 10 = true := by
  decide +kernel

theorem oddSum0562_checked :
    packedSumCheck packedFactorsOdd (row0562.map Prod.snd) oddDots0562 641 10 = true := by
  decide +kernel

theorem evenSum0563_checked :
    packedSumCheck packedFactorsEven (row0563.map Prod.fst) evenDots0563 641 10 = true := by
  decide +kernel

theorem oddSum0563_checked :
    packedSumCheck packedFactorsOdd (row0563.map Prod.snd) oddDots0563 641 10 = true := by
  decide +kernel

theorem evenSum0564_checked :
    packedSumCheck packedFactorsEven (row0564.map Prod.fst) evenDots0564 641 10 = true := by
  decide +kernel

theorem oddSum0564_checked :
    packedSumCheck packedFactorsOdd (row0564.map Prod.snd) oddDots0564 641 10 = true := by
  decide +kernel

theorem evenSum0565_checked :
    packedSumCheck packedFactorsEven (row0565.map Prod.fst) evenDots0565 641 10 = true := by
  decide +kernel

theorem oddSum0565_checked :
    packedSumCheck packedFactorsOdd (row0565.map Prod.snd) oddDots0565 641 10 = true := by
  decide +kernel

theorem evenSum0566_checked :
    packedSumCheck packedFactorsEven (row0566.map Prod.fst) evenDots0566 641 10 = true := by
  decide +kernel

theorem oddSum0566_checked :
    packedSumCheck packedFactorsOdd (row0566.map Prod.snd) oddDots0566 641 10 = true := by
  decide +kernel

theorem evenSum0567_checked :
    packedSumCheck packedFactorsEven (row0567.map Prod.fst) evenDots0567 641 10 = true := by
  decide +kernel

theorem oddSum0567_checked :
    packedSumCheck packedFactorsOdd (row0567.map Prod.snd) oddDots0567 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
