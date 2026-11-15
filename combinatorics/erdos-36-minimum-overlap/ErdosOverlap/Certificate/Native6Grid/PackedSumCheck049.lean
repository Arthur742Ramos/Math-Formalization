module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows049
public import ErdosOverlap.Certificate.Native6Grid.PackedDots049

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0392_checked :
    packedSumCheck packedFactorsEven (row0392.map Prod.fst) evenDots0392 641 10 = true := by
  decide +kernel

theorem oddSum0392_checked :
    packedSumCheck packedFactorsOdd (row0392.map Prod.snd) oddDots0392 641 10 = true := by
  decide +kernel

theorem evenSum0393_checked :
    packedSumCheck packedFactorsEven (row0393.map Prod.fst) evenDots0393 641 10 = true := by
  decide +kernel

theorem oddSum0393_checked :
    packedSumCheck packedFactorsOdd (row0393.map Prod.snd) oddDots0393 641 10 = true := by
  decide +kernel

theorem evenSum0394_checked :
    packedSumCheck packedFactorsEven (row0394.map Prod.fst) evenDots0394 641 10 = true := by
  decide +kernel

theorem oddSum0394_checked :
    packedSumCheck packedFactorsOdd (row0394.map Prod.snd) oddDots0394 641 10 = true := by
  decide +kernel

theorem evenSum0395_checked :
    packedSumCheck packedFactorsEven (row0395.map Prod.fst) evenDots0395 641 10 = true := by
  decide +kernel

theorem oddSum0395_checked :
    packedSumCheck packedFactorsOdd (row0395.map Prod.snd) oddDots0395 641 10 = true := by
  decide +kernel

theorem evenSum0396_checked :
    packedSumCheck packedFactorsEven (row0396.map Prod.fst) evenDots0396 641 10 = true := by
  decide +kernel

theorem oddSum0396_checked :
    packedSumCheck packedFactorsOdd (row0396.map Prod.snd) oddDots0396 641 10 = true := by
  decide +kernel

theorem evenSum0397_checked :
    packedSumCheck packedFactorsEven (row0397.map Prod.fst) evenDots0397 641 10 = true := by
  decide +kernel

theorem oddSum0397_checked :
    packedSumCheck packedFactorsOdd (row0397.map Prod.snd) oddDots0397 641 10 = true := by
  decide +kernel

theorem evenSum0398_checked :
    packedSumCheck packedFactorsEven (row0398.map Prod.fst) evenDots0398 641 10 = true := by
  decide +kernel

theorem oddSum0398_checked :
    packedSumCheck packedFactorsOdd (row0398.map Prod.snd) oddDots0398 641 10 = true := by
  decide +kernel

theorem evenSum0399_checked :
    packedSumCheck packedFactorsEven (row0399.map Prod.fst) evenDots0399 641 10 = true := by
  decide +kernel

theorem oddSum0399_checked :
    packedSumCheck packedFactorsOdd (row0399.map Prod.snd) oddDots0399 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
