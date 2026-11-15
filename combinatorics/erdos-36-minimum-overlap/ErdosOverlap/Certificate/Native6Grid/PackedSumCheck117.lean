module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows117
public import ErdosOverlap.Certificate.Native6Grid.PackedDots117

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0936_checked :
    packedSumCheck packedFactorsEven (row0936.map Prod.fst) evenDots0936 641 10 = true := by
  decide +kernel

theorem oddSum0936_checked :
    packedSumCheck packedFactorsOdd (row0936.map Prod.snd) oddDots0936 641 10 = true := by
  decide +kernel

theorem evenSum0937_checked :
    packedSumCheck packedFactorsEven (row0937.map Prod.fst) evenDots0937 641 10 = true := by
  decide +kernel

theorem oddSum0937_checked :
    packedSumCheck packedFactorsOdd (row0937.map Prod.snd) oddDots0937 641 10 = true := by
  decide +kernel

theorem evenSum0938_checked :
    packedSumCheck packedFactorsEven (row0938.map Prod.fst) evenDots0938 641 10 = true := by
  decide +kernel

theorem oddSum0938_checked :
    packedSumCheck packedFactorsOdd (row0938.map Prod.snd) oddDots0938 641 10 = true := by
  decide +kernel

theorem evenSum0939_checked :
    packedSumCheck packedFactorsEven (row0939.map Prod.fst) evenDots0939 641 10 = true := by
  decide +kernel

theorem oddSum0939_checked :
    packedSumCheck packedFactorsOdd (row0939.map Prod.snd) oddDots0939 641 10 = true := by
  decide +kernel

theorem evenSum0940_checked :
    packedSumCheck packedFactorsEven (row0940.map Prod.fst) evenDots0940 641 10 = true := by
  decide +kernel

theorem oddSum0940_checked :
    packedSumCheck packedFactorsOdd (row0940.map Prod.snd) oddDots0940 641 10 = true := by
  decide +kernel

theorem evenSum0941_checked :
    packedSumCheck packedFactorsEven (row0941.map Prod.fst) evenDots0941 641 10 = true := by
  decide +kernel

theorem oddSum0941_checked :
    packedSumCheck packedFactorsOdd (row0941.map Prod.snd) oddDots0941 641 10 = true := by
  decide +kernel

theorem evenSum0942_checked :
    packedSumCheck packedFactorsEven (row0942.map Prod.fst) evenDots0942 641 10 = true := by
  decide +kernel

theorem oddSum0942_checked :
    packedSumCheck packedFactorsOdd (row0942.map Prod.snd) oddDots0942 641 10 = true := by
  decide +kernel

theorem evenSum0943_checked :
    packedSumCheck packedFactorsEven (row0943.map Prod.fst) evenDots0943 641 10 = true := by
  decide +kernel

theorem oddSum0943_checked :
    packedSumCheck packedFactorsOdd (row0943.map Prod.snd) oddDots0943 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
