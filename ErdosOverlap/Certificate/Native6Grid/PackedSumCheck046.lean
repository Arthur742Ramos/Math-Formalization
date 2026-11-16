module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows046
public import ErdosOverlap.Certificate.Native6Grid.PackedDots046

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0368_checked :
    packedSumCheck packedFactorsEven (row0368.map Prod.fst) evenDots0368 641 10 = true := by
  decide +kernel

theorem oddSum0368_checked :
    packedSumCheck packedFactorsOdd (row0368.map Prod.snd) oddDots0368 641 10 = true := by
  decide +kernel

theorem evenSum0369_checked :
    packedSumCheck packedFactorsEven (row0369.map Prod.fst) evenDots0369 641 10 = true := by
  decide +kernel

theorem oddSum0369_checked :
    packedSumCheck packedFactorsOdd (row0369.map Prod.snd) oddDots0369 641 10 = true := by
  decide +kernel

theorem evenSum0370_checked :
    packedSumCheck packedFactorsEven (row0370.map Prod.fst) evenDots0370 641 10 = true := by
  decide +kernel

theorem oddSum0370_checked :
    packedSumCheck packedFactorsOdd (row0370.map Prod.snd) oddDots0370 641 10 = true := by
  decide +kernel

theorem evenSum0371_checked :
    packedSumCheck packedFactorsEven (row0371.map Prod.fst) evenDots0371 641 10 = true := by
  decide +kernel

theorem oddSum0371_checked :
    packedSumCheck packedFactorsOdd (row0371.map Prod.snd) oddDots0371 641 10 = true := by
  decide +kernel

theorem evenSum0372_checked :
    packedSumCheck packedFactorsEven (row0372.map Prod.fst) evenDots0372 641 10 = true := by
  decide +kernel

theorem oddSum0372_checked :
    packedSumCheck packedFactorsOdd (row0372.map Prod.snd) oddDots0372 641 10 = true := by
  decide +kernel

theorem evenSum0373_checked :
    packedSumCheck packedFactorsEven (row0373.map Prod.fst) evenDots0373 641 10 = true := by
  decide +kernel

theorem oddSum0373_checked :
    packedSumCheck packedFactorsOdd (row0373.map Prod.snd) oddDots0373 641 10 = true := by
  decide +kernel

theorem evenSum0374_checked :
    packedSumCheck packedFactorsEven (row0374.map Prod.fst) evenDots0374 641 10 = true := by
  decide +kernel

theorem oddSum0374_checked :
    packedSumCheck packedFactorsOdd (row0374.map Prod.snd) oddDots0374 641 10 = true := by
  decide +kernel

theorem evenSum0375_checked :
    packedSumCheck packedFactorsEven (row0375.map Prod.fst) evenDots0375 641 10 = true := by
  decide +kernel

theorem oddSum0375_checked :
    packedSumCheck packedFactorsOdd (row0375.map Prod.snd) oddDots0375 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
