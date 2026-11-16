module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows032
public import ErdosOverlap.Certificate.Native6Grid.PackedDots032

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0256_checked :
    packedSumCheck packedFactorsEven (row0256.map Prod.fst) evenDots0256 641 10 = true := by
  decide +kernel

theorem oddSum0256_checked :
    packedSumCheck packedFactorsOdd (row0256.map Prod.snd) oddDots0256 641 10 = true := by
  decide +kernel

theorem evenSum0257_checked :
    packedSumCheck packedFactorsEven (row0257.map Prod.fst) evenDots0257 641 10 = true := by
  decide +kernel

theorem oddSum0257_checked :
    packedSumCheck packedFactorsOdd (row0257.map Prod.snd) oddDots0257 641 10 = true := by
  decide +kernel

theorem evenSum0258_checked :
    packedSumCheck packedFactorsEven (row0258.map Prod.fst) evenDots0258 641 10 = true := by
  decide +kernel

theorem oddSum0258_checked :
    packedSumCheck packedFactorsOdd (row0258.map Prod.snd) oddDots0258 641 10 = true := by
  decide +kernel

theorem evenSum0259_checked :
    packedSumCheck packedFactorsEven (row0259.map Prod.fst) evenDots0259 641 10 = true := by
  decide +kernel

theorem oddSum0259_checked :
    packedSumCheck packedFactorsOdd (row0259.map Prod.snd) oddDots0259 641 10 = true := by
  decide +kernel

theorem evenSum0260_checked :
    packedSumCheck packedFactorsEven (row0260.map Prod.fst) evenDots0260 641 10 = true := by
  decide +kernel

theorem oddSum0260_checked :
    packedSumCheck packedFactorsOdd (row0260.map Prod.snd) oddDots0260 641 10 = true := by
  decide +kernel

theorem evenSum0261_checked :
    packedSumCheck packedFactorsEven (row0261.map Prod.fst) evenDots0261 641 10 = true := by
  decide +kernel

theorem oddSum0261_checked :
    packedSumCheck packedFactorsOdd (row0261.map Prod.snd) oddDots0261 641 10 = true := by
  decide +kernel

theorem evenSum0262_checked :
    packedSumCheck packedFactorsEven (row0262.map Prod.fst) evenDots0262 641 10 = true := by
  decide +kernel

theorem oddSum0262_checked :
    packedSumCheck packedFactorsOdd (row0262.map Prod.snd) oddDots0262 641 10 = true := by
  decide +kernel

theorem evenSum0263_checked :
    packedSumCheck packedFactorsEven (row0263.map Prod.fst) evenDots0263 641 10 = true := by
  decide +kernel

theorem oddSum0263_checked :
    packedSumCheck packedFactorsOdd (row0263.map Prod.snd) oddDots0263 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
