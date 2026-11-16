module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows058
public import ErdosOverlap.Certificate.Native6Grid.PackedDots058

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0464_checked :
    packedSumCheck packedFactorsEven (row0464.map Prod.fst) evenDots0464 641 10 = true := by
  decide +kernel

theorem oddSum0464_checked :
    packedSumCheck packedFactorsOdd (row0464.map Prod.snd) oddDots0464 641 10 = true := by
  decide +kernel

theorem evenSum0465_checked :
    packedSumCheck packedFactorsEven (row0465.map Prod.fst) evenDots0465 641 10 = true := by
  decide +kernel

theorem oddSum0465_checked :
    packedSumCheck packedFactorsOdd (row0465.map Prod.snd) oddDots0465 641 10 = true := by
  decide +kernel

theorem evenSum0466_checked :
    packedSumCheck packedFactorsEven (row0466.map Prod.fst) evenDots0466 641 10 = true := by
  decide +kernel

theorem oddSum0466_checked :
    packedSumCheck packedFactorsOdd (row0466.map Prod.snd) oddDots0466 641 10 = true := by
  decide +kernel

theorem evenSum0467_checked :
    packedSumCheck packedFactorsEven (row0467.map Prod.fst) evenDots0467 641 10 = true := by
  decide +kernel

theorem oddSum0467_checked :
    packedSumCheck packedFactorsOdd (row0467.map Prod.snd) oddDots0467 641 10 = true := by
  decide +kernel

theorem evenSum0468_checked :
    packedSumCheck packedFactorsEven (row0468.map Prod.fst) evenDots0468 641 10 = true := by
  decide +kernel

theorem oddSum0468_checked :
    packedSumCheck packedFactorsOdd (row0468.map Prod.snd) oddDots0468 641 10 = true := by
  decide +kernel

theorem evenSum0469_checked :
    packedSumCheck packedFactorsEven (row0469.map Prod.fst) evenDots0469 641 10 = true := by
  decide +kernel

theorem oddSum0469_checked :
    packedSumCheck packedFactorsOdd (row0469.map Prod.snd) oddDots0469 641 10 = true := by
  decide +kernel

theorem evenSum0470_checked :
    packedSumCheck packedFactorsEven (row0470.map Prod.fst) evenDots0470 641 10 = true := by
  decide +kernel

theorem oddSum0470_checked :
    packedSumCheck packedFactorsOdd (row0470.map Prod.snd) oddDots0470 641 10 = true := by
  decide +kernel

theorem evenSum0471_checked :
    packedSumCheck packedFactorsEven (row0471.map Prod.fst) evenDots0471 641 10 = true := by
  decide +kernel

theorem oddSum0471_checked :
    packedSumCheck packedFactorsOdd (row0471.map Prod.snd) oddDots0471 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
