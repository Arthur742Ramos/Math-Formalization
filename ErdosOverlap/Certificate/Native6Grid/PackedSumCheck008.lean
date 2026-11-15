module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows008
public import ErdosOverlap.Certificate.Native6Grid.PackedDots008

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0064_checked :
    packedSumCheck packedFactorsEven (row0064.map Prod.fst) evenDots0064 641 10 = true := by
  decide +kernel

theorem oddSum0064_checked :
    packedSumCheck packedFactorsOdd (row0064.map Prod.snd) oddDots0064 641 10 = true := by
  decide +kernel

theorem evenSum0065_checked :
    packedSumCheck packedFactorsEven (row0065.map Prod.fst) evenDots0065 641 10 = true := by
  decide +kernel

theorem oddSum0065_checked :
    packedSumCheck packedFactorsOdd (row0065.map Prod.snd) oddDots0065 641 10 = true := by
  decide +kernel

theorem evenSum0066_checked :
    packedSumCheck packedFactorsEven (row0066.map Prod.fst) evenDots0066 641 10 = true := by
  decide +kernel

theorem oddSum0066_checked :
    packedSumCheck packedFactorsOdd (row0066.map Prod.snd) oddDots0066 641 10 = true := by
  decide +kernel

theorem evenSum0067_checked :
    packedSumCheck packedFactorsEven (row0067.map Prod.fst) evenDots0067 641 10 = true := by
  decide +kernel

theorem oddSum0067_checked :
    packedSumCheck packedFactorsOdd (row0067.map Prod.snd) oddDots0067 641 10 = true := by
  decide +kernel

theorem evenSum0068_checked :
    packedSumCheck packedFactorsEven (row0068.map Prod.fst) evenDots0068 641 10 = true := by
  decide +kernel

theorem oddSum0068_checked :
    packedSumCheck packedFactorsOdd (row0068.map Prod.snd) oddDots0068 641 10 = true := by
  decide +kernel

theorem evenSum0069_checked :
    packedSumCheck packedFactorsEven (row0069.map Prod.fst) evenDots0069 641 10 = true := by
  decide +kernel

theorem oddSum0069_checked :
    packedSumCheck packedFactorsOdd (row0069.map Prod.snd) oddDots0069 641 10 = true := by
  decide +kernel

theorem evenSum0070_checked :
    packedSumCheck packedFactorsEven (row0070.map Prod.fst) evenDots0070 641 10 = true := by
  decide +kernel

theorem oddSum0070_checked :
    packedSumCheck packedFactorsOdd (row0070.map Prod.snd) oddDots0070 641 10 = true := by
  decide +kernel

theorem evenSum0071_checked :
    packedSumCheck packedFactorsEven (row0071.map Prod.fst) evenDots0071 641 10 = true := by
  decide +kernel

theorem oddSum0071_checked :
    packedSumCheck packedFactorsOdd (row0071.map Prod.snd) oddDots0071 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
