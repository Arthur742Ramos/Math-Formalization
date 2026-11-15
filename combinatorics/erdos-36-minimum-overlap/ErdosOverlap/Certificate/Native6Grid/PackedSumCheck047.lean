module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows047
public import ErdosOverlap.Certificate.Native6Grid.PackedDots047

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0376_checked :
    packedSumCheck packedFactorsEven (row0376.map Prod.fst) evenDots0376 641 10 = true := by
  decide +kernel

theorem oddSum0376_checked :
    packedSumCheck packedFactorsOdd (row0376.map Prod.snd) oddDots0376 641 10 = true := by
  decide +kernel

theorem evenSum0377_checked :
    packedSumCheck packedFactorsEven (row0377.map Prod.fst) evenDots0377 641 10 = true := by
  decide +kernel

theorem oddSum0377_checked :
    packedSumCheck packedFactorsOdd (row0377.map Prod.snd) oddDots0377 641 10 = true := by
  decide +kernel

theorem evenSum0378_checked :
    packedSumCheck packedFactorsEven (row0378.map Prod.fst) evenDots0378 641 10 = true := by
  decide +kernel

theorem oddSum0378_checked :
    packedSumCheck packedFactorsOdd (row0378.map Prod.snd) oddDots0378 641 10 = true := by
  decide +kernel

theorem evenSum0379_checked :
    packedSumCheck packedFactorsEven (row0379.map Prod.fst) evenDots0379 641 10 = true := by
  decide +kernel

theorem oddSum0379_checked :
    packedSumCheck packedFactorsOdd (row0379.map Prod.snd) oddDots0379 641 10 = true := by
  decide +kernel

theorem evenSum0380_checked :
    packedSumCheck packedFactorsEven (row0380.map Prod.fst) evenDots0380 641 10 = true := by
  decide +kernel

theorem oddSum0380_checked :
    packedSumCheck packedFactorsOdd (row0380.map Prod.snd) oddDots0380 641 10 = true := by
  decide +kernel

theorem evenSum0381_checked :
    packedSumCheck packedFactorsEven (row0381.map Prod.fst) evenDots0381 641 10 = true := by
  decide +kernel

theorem oddSum0381_checked :
    packedSumCheck packedFactorsOdd (row0381.map Prod.snd) oddDots0381 641 10 = true := by
  decide +kernel

theorem evenSum0382_checked :
    packedSumCheck packedFactorsEven (row0382.map Prod.fst) evenDots0382 641 10 = true := by
  decide +kernel

theorem oddSum0382_checked :
    packedSumCheck packedFactorsOdd (row0382.map Prod.snd) oddDots0382 641 10 = true := by
  decide +kernel

theorem evenSum0383_checked :
    packedSumCheck packedFactorsEven (row0383.map Prod.fst) evenDots0383 641 10 = true := by
  decide +kernel

theorem oddSum0383_checked :
    packedSumCheck packedFactorsOdd (row0383.map Prod.snd) oddDots0383 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
