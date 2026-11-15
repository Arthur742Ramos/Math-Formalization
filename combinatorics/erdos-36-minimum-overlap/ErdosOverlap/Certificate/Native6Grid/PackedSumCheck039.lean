module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows039
public import ErdosOverlap.Certificate.Native6Grid.PackedDots039

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0312_checked :
    packedSumCheck packedFactorsEven (row0312.map Prod.fst) evenDots0312 641 10 = true := by
  decide +kernel

theorem oddSum0312_checked :
    packedSumCheck packedFactorsOdd (row0312.map Prod.snd) oddDots0312 641 10 = true := by
  decide +kernel

theorem evenSum0313_checked :
    packedSumCheck packedFactorsEven (row0313.map Prod.fst) evenDots0313 641 10 = true := by
  decide +kernel

theorem oddSum0313_checked :
    packedSumCheck packedFactorsOdd (row0313.map Prod.snd) oddDots0313 641 10 = true := by
  decide +kernel

theorem evenSum0314_checked :
    packedSumCheck packedFactorsEven (row0314.map Prod.fst) evenDots0314 641 10 = true := by
  decide +kernel

theorem oddSum0314_checked :
    packedSumCheck packedFactorsOdd (row0314.map Prod.snd) oddDots0314 641 10 = true := by
  decide +kernel

theorem evenSum0315_checked :
    packedSumCheck packedFactorsEven (row0315.map Prod.fst) evenDots0315 641 10 = true := by
  decide +kernel

theorem oddSum0315_checked :
    packedSumCheck packedFactorsOdd (row0315.map Prod.snd) oddDots0315 641 10 = true := by
  decide +kernel

theorem evenSum0316_checked :
    packedSumCheck packedFactorsEven (row0316.map Prod.fst) evenDots0316 641 10 = true := by
  decide +kernel

theorem oddSum0316_checked :
    packedSumCheck packedFactorsOdd (row0316.map Prod.snd) oddDots0316 641 10 = true := by
  decide +kernel

theorem evenSum0317_checked :
    packedSumCheck packedFactorsEven (row0317.map Prod.fst) evenDots0317 641 10 = true := by
  decide +kernel

theorem oddSum0317_checked :
    packedSumCheck packedFactorsOdd (row0317.map Prod.snd) oddDots0317 641 10 = true := by
  decide +kernel

theorem evenSum0318_checked :
    packedSumCheck packedFactorsEven (row0318.map Prod.fst) evenDots0318 641 10 = true := by
  decide +kernel

theorem oddSum0318_checked :
    packedSumCheck packedFactorsOdd (row0318.map Prod.snd) oddDots0318 641 10 = true := by
  decide +kernel

theorem evenSum0319_checked :
    packedSumCheck packedFactorsEven (row0319.map Prod.fst) evenDots0319 641 10 = true := by
  decide +kernel

theorem oddSum0319_checked :
    packedSumCheck packedFactorsOdd (row0319.map Prod.snd) oddDots0319 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
