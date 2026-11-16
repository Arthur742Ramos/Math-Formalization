module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows024
public import ErdosOverlap.Certificate.Native6Grid.PackedDots024

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0192_checked :
    packedSumCheck packedFactorsEven (row0192.map Prod.fst) evenDots0192 641 10 = true := by
  decide +kernel

theorem oddSum0192_checked :
    packedSumCheck packedFactorsOdd (row0192.map Prod.snd) oddDots0192 641 10 = true := by
  decide +kernel

theorem evenSum0193_checked :
    packedSumCheck packedFactorsEven (row0193.map Prod.fst) evenDots0193 641 10 = true := by
  decide +kernel

theorem oddSum0193_checked :
    packedSumCheck packedFactorsOdd (row0193.map Prod.snd) oddDots0193 641 10 = true := by
  decide +kernel

theorem evenSum0194_checked :
    packedSumCheck packedFactorsEven (row0194.map Prod.fst) evenDots0194 641 10 = true := by
  decide +kernel

theorem oddSum0194_checked :
    packedSumCheck packedFactorsOdd (row0194.map Prod.snd) oddDots0194 641 10 = true := by
  decide +kernel

theorem evenSum0195_checked :
    packedSumCheck packedFactorsEven (row0195.map Prod.fst) evenDots0195 641 10 = true := by
  decide +kernel

theorem oddSum0195_checked :
    packedSumCheck packedFactorsOdd (row0195.map Prod.snd) oddDots0195 641 10 = true := by
  decide +kernel

theorem evenSum0196_checked :
    packedSumCheck packedFactorsEven (row0196.map Prod.fst) evenDots0196 641 10 = true := by
  decide +kernel

theorem oddSum0196_checked :
    packedSumCheck packedFactorsOdd (row0196.map Prod.snd) oddDots0196 641 10 = true := by
  decide +kernel

theorem evenSum0197_checked :
    packedSumCheck packedFactorsEven (row0197.map Prod.fst) evenDots0197 641 10 = true := by
  decide +kernel

theorem oddSum0197_checked :
    packedSumCheck packedFactorsOdd (row0197.map Prod.snd) oddDots0197 641 10 = true := by
  decide +kernel

theorem evenSum0198_checked :
    packedSumCheck packedFactorsEven (row0198.map Prod.fst) evenDots0198 641 10 = true := by
  decide +kernel

theorem oddSum0198_checked :
    packedSumCheck packedFactorsOdd (row0198.map Prod.snd) oddDots0198 641 10 = true := by
  decide +kernel

theorem evenSum0199_checked :
    packedSumCheck packedFactorsEven (row0199.map Prod.fst) evenDots0199 641 10 = true := by
  decide +kernel

theorem oddSum0199_checked :
    packedSumCheck packedFactorsOdd (row0199.map Prod.snd) oddDots0199 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
