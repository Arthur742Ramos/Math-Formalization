module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows027
public import ErdosOverlap.Certificate.Native6Grid.PackedDots027

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0216_checked :
    packedSumCheck packedFactorsEven (row0216.map Prod.fst) evenDots0216 641 10 = true := by
  decide +kernel

theorem oddSum0216_checked :
    packedSumCheck packedFactorsOdd (row0216.map Prod.snd) oddDots0216 641 10 = true := by
  decide +kernel

theorem evenSum0217_checked :
    packedSumCheck packedFactorsEven (row0217.map Prod.fst) evenDots0217 641 10 = true := by
  decide +kernel

theorem oddSum0217_checked :
    packedSumCheck packedFactorsOdd (row0217.map Prod.snd) oddDots0217 641 10 = true := by
  decide +kernel

theorem evenSum0218_checked :
    packedSumCheck packedFactorsEven (row0218.map Prod.fst) evenDots0218 641 10 = true := by
  decide +kernel

theorem oddSum0218_checked :
    packedSumCheck packedFactorsOdd (row0218.map Prod.snd) oddDots0218 641 10 = true := by
  decide +kernel

theorem evenSum0219_checked :
    packedSumCheck packedFactorsEven (row0219.map Prod.fst) evenDots0219 641 10 = true := by
  decide +kernel

theorem oddSum0219_checked :
    packedSumCheck packedFactorsOdd (row0219.map Prod.snd) oddDots0219 641 10 = true := by
  decide +kernel

theorem evenSum0220_checked :
    packedSumCheck packedFactorsEven (row0220.map Prod.fst) evenDots0220 641 10 = true := by
  decide +kernel

theorem oddSum0220_checked :
    packedSumCheck packedFactorsOdd (row0220.map Prod.snd) oddDots0220 641 10 = true := by
  decide +kernel

theorem evenSum0221_checked :
    packedSumCheck packedFactorsEven (row0221.map Prod.fst) evenDots0221 641 10 = true := by
  decide +kernel

theorem oddSum0221_checked :
    packedSumCheck packedFactorsOdd (row0221.map Prod.snd) oddDots0221 641 10 = true := by
  decide +kernel

theorem evenSum0222_checked :
    packedSumCheck packedFactorsEven (row0222.map Prod.fst) evenDots0222 641 10 = true := by
  decide +kernel

theorem oddSum0222_checked :
    packedSumCheck packedFactorsOdd (row0222.map Prod.snd) oddDots0222 641 10 = true := by
  decide +kernel

theorem evenSum0223_checked :
    packedSumCheck packedFactorsEven (row0223.map Prod.fst) evenDots0223 641 10 = true := by
  decide +kernel

theorem oddSum0223_checked :
    packedSumCheck packedFactorsOdd (row0223.map Prod.snd) oddDots0223 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
