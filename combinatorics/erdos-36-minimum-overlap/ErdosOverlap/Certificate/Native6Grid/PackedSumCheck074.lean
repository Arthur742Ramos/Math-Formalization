module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows074
public import ErdosOverlap.Certificate.Native6Grid.PackedDots074

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0592_checked :
    packedSumCheck packedFactorsEven (row0592.map Prod.fst) evenDots0592 641 10 = true := by
  decide +kernel

theorem oddSum0592_checked :
    packedSumCheck packedFactorsOdd (row0592.map Prod.snd) oddDots0592 641 10 = true := by
  decide +kernel

theorem evenSum0593_checked :
    packedSumCheck packedFactorsEven (row0593.map Prod.fst) evenDots0593 641 10 = true := by
  decide +kernel

theorem oddSum0593_checked :
    packedSumCheck packedFactorsOdd (row0593.map Prod.snd) oddDots0593 641 10 = true := by
  decide +kernel

theorem evenSum0594_checked :
    packedSumCheck packedFactorsEven (row0594.map Prod.fst) evenDots0594 641 10 = true := by
  decide +kernel

theorem oddSum0594_checked :
    packedSumCheck packedFactorsOdd (row0594.map Prod.snd) oddDots0594 641 10 = true := by
  decide +kernel

theorem evenSum0595_checked :
    packedSumCheck packedFactorsEven (row0595.map Prod.fst) evenDots0595 641 10 = true := by
  decide +kernel

theorem oddSum0595_checked :
    packedSumCheck packedFactorsOdd (row0595.map Prod.snd) oddDots0595 641 10 = true := by
  decide +kernel

theorem evenSum0596_checked :
    packedSumCheck packedFactorsEven (row0596.map Prod.fst) evenDots0596 641 10 = true := by
  decide +kernel

theorem oddSum0596_checked :
    packedSumCheck packedFactorsOdd (row0596.map Prod.snd) oddDots0596 641 10 = true := by
  decide +kernel

theorem evenSum0597_checked :
    packedSumCheck packedFactorsEven (row0597.map Prod.fst) evenDots0597 641 10 = true := by
  decide +kernel

theorem oddSum0597_checked :
    packedSumCheck packedFactorsOdd (row0597.map Prod.snd) oddDots0597 641 10 = true := by
  decide +kernel

theorem evenSum0598_checked :
    packedSumCheck packedFactorsEven (row0598.map Prod.fst) evenDots0598 641 10 = true := by
  decide +kernel

theorem oddSum0598_checked :
    packedSumCheck packedFactorsOdd (row0598.map Prod.snd) oddDots0598 641 10 = true := by
  decide +kernel

theorem evenSum0599_checked :
    packedSumCheck packedFactorsEven (row0599.map Prod.fst) evenDots0599 641 10 = true := by
  decide +kernel

theorem oddSum0599_checked :
    packedSumCheck packedFactorsOdd (row0599.map Prod.snd) oddDots0599 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
