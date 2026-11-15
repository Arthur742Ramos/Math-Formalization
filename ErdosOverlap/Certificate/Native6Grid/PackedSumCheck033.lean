module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows033
public import ErdosOverlap.Certificate.Native6Grid.PackedDots033

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0264_checked :
    packedSumCheck packedFactorsEven (row0264.map Prod.fst) evenDots0264 641 10 = true := by
  decide +kernel

theorem oddSum0264_checked :
    packedSumCheck packedFactorsOdd (row0264.map Prod.snd) oddDots0264 641 10 = true := by
  decide +kernel

theorem evenSum0265_checked :
    packedSumCheck packedFactorsEven (row0265.map Prod.fst) evenDots0265 641 10 = true := by
  decide +kernel

theorem oddSum0265_checked :
    packedSumCheck packedFactorsOdd (row0265.map Prod.snd) oddDots0265 641 10 = true := by
  decide +kernel

theorem evenSum0266_checked :
    packedSumCheck packedFactorsEven (row0266.map Prod.fst) evenDots0266 641 10 = true := by
  decide +kernel

theorem oddSum0266_checked :
    packedSumCheck packedFactorsOdd (row0266.map Prod.snd) oddDots0266 641 10 = true := by
  decide +kernel

theorem evenSum0267_checked :
    packedSumCheck packedFactorsEven (row0267.map Prod.fst) evenDots0267 641 10 = true := by
  decide +kernel

theorem oddSum0267_checked :
    packedSumCheck packedFactorsOdd (row0267.map Prod.snd) oddDots0267 641 10 = true := by
  decide +kernel

theorem evenSum0268_checked :
    packedSumCheck packedFactorsEven (row0268.map Prod.fst) evenDots0268 641 10 = true := by
  decide +kernel

theorem oddSum0268_checked :
    packedSumCheck packedFactorsOdd (row0268.map Prod.snd) oddDots0268 641 10 = true := by
  decide +kernel

theorem evenSum0269_checked :
    packedSumCheck packedFactorsEven (row0269.map Prod.fst) evenDots0269 641 10 = true := by
  decide +kernel

theorem oddSum0269_checked :
    packedSumCheck packedFactorsOdd (row0269.map Prod.snd) oddDots0269 641 10 = true := by
  decide +kernel

theorem evenSum0270_checked :
    packedSumCheck packedFactorsEven (row0270.map Prod.fst) evenDots0270 641 10 = true := by
  decide +kernel

theorem oddSum0270_checked :
    packedSumCheck packedFactorsOdd (row0270.map Prod.snd) oddDots0270 641 10 = true := by
  decide +kernel

theorem evenSum0271_checked :
    packedSumCheck packedFactorsEven (row0271.map Prod.fst) evenDots0271 641 10 = true := by
  decide +kernel

theorem oddSum0271_checked :
    packedSumCheck packedFactorsOdd (row0271.map Prod.snd) oddDots0271 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
