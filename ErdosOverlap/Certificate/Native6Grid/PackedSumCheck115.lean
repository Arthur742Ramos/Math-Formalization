module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows115
public import ErdosOverlap.Certificate.Native6Grid.PackedDots115

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0920_checked :
    packedSumCheck packedFactorsEven (row0920.map Prod.fst) evenDots0920 641 10 = true := by
  decide +kernel

theorem oddSum0920_checked :
    packedSumCheck packedFactorsOdd (row0920.map Prod.snd) oddDots0920 641 10 = true := by
  decide +kernel

theorem evenSum0921_checked :
    packedSumCheck packedFactorsEven (row0921.map Prod.fst) evenDots0921 641 10 = true := by
  decide +kernel

theorem oddSum0921_checked :
    packedSumCheck packedFactorsOdd (row0921.map Prod.snd) oddDots0921 641 10 = true := by
  decide +kernel

theorem evenSum0922_checked :
    packedSumCheck packedFactorsEven (row0922.map Prod.fst) evenDots0922 641 10 = true := by
  decide +kernel

theorem oddSum0922_checked :
    packedSumCheck packedFactorsOdd (row0922.map Prod.snd) oddDots0922 641 10 = true := by
  decide +kernel

theorem evenSum0923_checked :
    packedSumCheck packedFactorsEven (row0923.map Prod.fst) evenDots0923 641 10 = true := by
  decide +kernel

theorem oddSum0923_checked :
    packedSumCheck packedFactorsOdd (row0923.map Prod.snd) oddDots0923 641 10 = true := by
  decide +kernel

theorem evenSum0924_checked :
    packedSumCheck packedFactorsEven (row0924.map Prod.fst) evenDots0924 641 10 = true := by
  decide +kernel

theorem oddSum0924_checked :
    packedSumCheck packedFactorsOdd (row0924.map Prod.snd) oddDots0924 641 10 = true := by
  decide +kernel

theorem evenSum0925_checked :
    packedSumCheck packedFactorsEven (row0925.map Prod.fst) evenDots0925 641 10 = true := by
  decide +kernel

theorem oddSum0925_checked :
    packedSumCheck packedFactorsOdd (row0925.map Prod.snd) oddDots0925 641 10 = true := by
  decide +kernel

theorem evenSum0926_checked :
    packedSumCheck packedFactorsEven (row0926.map Prod.fst) evenDots0926 641 10 = true := by
  decide +kernel

theorem oddSum0926_checked :
    packedSumCheck packedFactorsOdd (row0926.map Prod.snd) oddDots0926 641 10 = true := by
  decide +kernel

theorem evenSum0927_checked :
    packedSumCheck packedFactorsEven (row0927.map Prod.fst) evenDots0927 641 10 = true := by
  decide +kernel

theorem oddSum0927_checked :
    packedSumCheck packedFactorsOdd (row0927.map Prod.snd) oddDots0927 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
