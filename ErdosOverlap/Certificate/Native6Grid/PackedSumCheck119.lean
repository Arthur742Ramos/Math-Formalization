module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows119
public import ErdosOverlap.Certificate.Native6Grid.PackedDots119

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0952_checked :
    packedSumCheck packedFactorsEven (row0952.map Prod.fst) evenDots0952 641 10 = true := by
  decide +kernel

theorem oddSum0952_checked :
    packedSumCheck packedFactorsOdd (row0952.map Prod.snd) oddDots0952 641 10 = true := by
  decide +kernel

theorem evenSum0953_checked :
    packedSumCheck packedFactorsEven (row0953.map Prod.fst) evenDots0953 641 10 = true := by
  decide +kernel

theorem oddSum0953_checked :
    packedSumCheck packedFactorsOdd (row0953.map Prod.snd) oddDots0953 641 10 = true := by
  decide +kernel

theorem evenSum0954_checked :
    packedSumCheck packedFactorsEven (row0954.map Prod.fst) evenDots0954 641 10 = true := by
  decide +kernel

theorem oddSum0954_checked :
    packedSumCheck packedFactorsOdd (row0954.map Prod.snd) oddDots0954 641 10 = true := by
  decide +kernel

theorem evenSum0955_checked :
    packedSumCheck packedFactorsEven (row0955.map Prod.fst) evenDots0955 641 10 = true := by
  decide +kernel

theorem oddSum0955_checked :
    packedSumCheck packedFactorsOdd (row0955.map Prod.snd) oddDots0955 641 10 = true := by
  decide +kernel

theorem evenSum0956_checked :
    packedSumCheck packedFactorsEven (row0956.map Prod.fst) evenDots0956 641 10 = true := by
  decide +kernel

theorem oddSum0956_checked :
    packedSumCheck packedFactorsOdd (row0956.map Prod.snd) oddDots0956 641 10 = true := by
  decide +kernel

theorem evenSum0957_checked :
    packedSumCheck packedFactorsEven (row0957.map Prod.fst) evenDots0957 641 10 = true := by
  decide +kernel

theorem oddSum0957_checked :
    packedSumCheck packedFactorsOdd (row0957.map Prod.snd) oddDots0957 641 10 = true := by
  decide +kernel

theorem evenSum0958_checked :
    packedSumCheck packedFactorsEven (row0958.map Prod.fst) evenDots0958 641 10 = true := by
  decide +kernel

theorem oddSum0958_checked :
    packedSumCheck packedFactorsOdd (row0958.map Prod.snd) oddDots0958 641 10 = true := by
  decide +kernel

theorem evenSum0959_checked :
    packedSumCheck packedFactorsEven (row0959.map Prod.fst) evenDots0959 641 10 = true := by
  decide +kernel

theorem oddSum0959_checked :
    packedSumCheck packedFactorsOdd (row0959.map Prod.snd) oddDots0959 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
