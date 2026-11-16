module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows081
public import ErdosOverlap.Certificate.Native6Grid.PackedDots081

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0648_checked :
    packedSumCheck packedFactorsEven (row0648.map Prod.fst) evenDots0648 641 10 = true := by
  decide +kernel

theorem oddSum0648_checked :
    packedSumCheck packedFactorsOdd (row0648.map Prod.snd) oddDots0648 641 10 = true := by
  decide +kernel

theorem evenSum0649_checked :
    packedSumCheck packedFactorsEven (row0649.map Prod.fst) evenDots0649 641 10 = true := by
  decide +kernel

theorem oddSum0649_checked :
    packedSumCheck packedFactorsOdd (row0649.map Prod.snd) oddDots0649 641 10 = true := by
  decide +kernel

theorem evenSum0650_checked :
    packedSumCheck packedFactorsEven (row0650.map Prod.fst) evenDots0650 641 10 = true := by
  decide +kernel

theorem oddSum0650_checked :
    packedSumCheck packedFactorsOdd (row0650.map Prod.snd) oddDots0650 641 10 = true := by
  decide +kernel

theorem evenSum0651_checked :
    packedSumCheck packedFactorsEven (row0651.map Prod.fst) evenDots0651 641 10 = true := by
  decide +kernel

theorem oddSum0651_checked :
    packedSumCheck packedFactorsOdd (row0651.map Prod.snd) oddDots0651 641 10 = true := by
  decide +kernel

theorem evenSum0652_checked :
    packedSumCheck packedFactorsEven (row0652.map Prod.fst) evenDots0652 641 10 = true := by
  decide +kernel

theorem oddSum0652_checked :
    packedSumCheck packedFactorsOdd (row0652.map Prod.snd) oddDots0652 641 10 = true := by
  decide +kernel

theorem evenSum0653_checked :
    packedSumCheck packedFactorsEven (row0653.map Prod.fst) evenDots0653 641 10 = true := by
  decide +kernel

theorem oddSum0653_checked :
    packedSumCheck packedFactorsOdd (row0653.map Prod.snd) oddDots0653 641 10 = true := by
  decide +kernel

theorem evenSum0654_checked :
    packedSumCheck packedFactorsEven (row0654.map Prod.fst) evenDots0654 641 10 = true := by
  decide +kernel

theorem oddSum0654_checked :
    packedSumCheck packedFactorsOdd (row0654.map Prod.snd) oddDots0654 641 10 = true := by
  decide +kernel

theorem evenSum0655_checked :
    packedSumCheck packedFactorsEven (row0655.map Prod.fst) evenDots0655 641 10 = true := by
  decide +kernel

theorem oddSum0655_checked :
    packedSumCheck packedFactorsOdd (row0655.map Prod.snd) oddDots0655 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
