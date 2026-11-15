module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows086
public import ErdosOverlap.Certificate.Native6Grid.PackedDots086

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0688_checked :
    packedSumCheck packedFactorsEven (row0688.map Prod.fst) evenDots0688 641 10 = true := by
  decide +kernel

theorem oddSum0688_checked :
    packedSumCheck packedFactorsOdd (row0688.map Prod.snd) oddDots0688 641 10 = true := by
  decide +kernel

theorem evenSum0689_checked :
    packedSumCheck packedFactorsEven (row0689.map Prod.fst) evenDots0689 641 10 = true := by
  decide +kernel

theorem oddSum0689_checked :
    packedSumCheck packedFactorsOdd (row0689.map Prod.snd) oddDots0689 641 10 = true := by
  decide +kernel

theorem evenSum0690_checked :
    packedSumCheck packedFactorsEven (row0690.map Prod.fst) evenDots0690 641 10 = true := by
  decide +kernel

theorem oddSum0690_checked :
    packedSumCheck packedFactorsOdd (row0690.map Prod.snd) oddDots0690 641 10 = true := by
  decide +kernel

theorem evenSum0691_checked :
    packedSumCheck packedFactorsEven (row0691.map Prod.fst) evenDots0691 641 10 = true := by
  decide +kernel

theorem oddSum0691_checked :
    packedSumCheck packedFactorsOdd (row0691.map Prod.snd) oddDots0691 641 10 = true := by
  decide +kernel

theorem evenSum0692_checked :
    packedSumCheck packedFactorsEven (row0692.map Prod.fst) evenDots0692 641 10 = true := by
  decide +kernel

theorem oddSum0692_checked :
    packedSumCheck packedFactorsOdd (row0692.map Prod.snd) oddDots0692 641 10 = true := by
  decide +kernel

theorem evenSum0693_checked :
    packedSumCheck packedFactorsEven (row0693.map Prod.fst) evenDots0693 641 10 = true := by
  decide +kernel

theorem oddSum0693_checked :
    packedSumCheck packedFactorsOdd (row0693.map Prod.snd) oddDots0693 641 10 = true := by
  decide +kernel

theorem evenSum0694_checked :
    packedSumCheck packedFactorsEven (row0694.map Prod.fst) evenDots0694 641 10 = true := by
  decide +kernel

theorem oddSum0694_checked :
    packedSumCheck packedFactorsOdd (row0694.map Prod.snd) oddDots0694 641 10 = true := by
  decide +kernel

theorem evenSum0695_checked :
    packedSumCheck packedFactorsEven (row0695.map Prod.fst) evenDots0695 641 10 = true := by
  decide +kernel

theorem oddSum0695_checked :
    packedSumCheck packedFactorsOdd (row0695.map Prod.snd) oddDots0695 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
