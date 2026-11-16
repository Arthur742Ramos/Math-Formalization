module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows029
public import ErdosOverlap.Certificate.Native6Grid.PackedDots029

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0232_checked :
    packedSumCheck packedFactorsEven (row0232.map Prod.fst) evenDots0232 641 10 = true := by
  decide +kernel

theorem oddSum0232_checked :
    packedSumCheck packedFactorsOdd (row0232.map Prod.snd) oddDots0232 641 10 = true := by
  decide +kernel

theorem evenSum0233_checked :
    packedSumCheck packedFactorsEven (row0233.map Prod.fst) evenDots0233 641 10 = true := by
  decide +kernel

theorem oddSum0233_checked :
    packedSumCheck packedFactorsOdd (row0233.map Prod.snd) oddDots0233 641 10 = true := by
  decide +kernel

theorem evenSum0234_checked :
    packedSumCheck packedFactorsEven (row0234.map Prod.fst) evenDots0234 641 10 = true := by
  decide +kernel

theorem oddSum0234_checked :
    packedSumCheck packedFactorsOdd (row0234.map Prod.snd) oddDots0234 641 10 = true := by
  decide +kernel

theorem evenSum0235_checked :
    packedSumCheck packedFactorsEven (row0235.map Prod.fst) evenDots0235 641 10 = true := by
  decide +kernel

theorem oddSum0235_checked :
    packedSumCheck packedFactorsOdd (row0235.map Prod.snd) oddDots0235 641 10 = true := by
  decide +kernel

theorem evenSum0236_checked :
    packedSumCheck packedFactorsEven (row0236.map Prod.fst) evenDots0236 641 10 = true := by
  decide +kernel

theorem oddSum0236_checked :
    packedSumCheck packedFactorsOdd (row0236.map Prod.snd) oddDots0236 641 10 = true := by
  decide +kernel

theorem evenSum0237_checked :
    packedSumCheck packedFactorsEven (row0237.map Prod.fst) evenDots0237 641 10 = true := by
  decide +kernel

theorem oddSum0237_checked :
    packedSumCheck packedFactorsOdd (row0237.map Prod.snd) oddDots0237 641 10 = true := by
  decide +kernel

theorem evenSum0238_checked :
    packedSumCheck packedFactorsEven (row0238.map Prod.fst) evenDots0238 641 10 = true := by
  decide +kernel

theorem oddSum0238_checked :
    packedSumCheck packedFactorsOdd (row0238.map Prod.snd) oddDots0238 641 10 = true := by
  decide +kernel

theorem evenSum0239_checked :
    packedSumCheck packedFactorsEven (row0239.map Prod.fst) evenDots0239 641 10 = true := by
  decide +kernel

theorem oddSum0239_checked :
    packedSumCheck packedFactorsOdd (row0239.map Prod.snd) oddDots0239 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
