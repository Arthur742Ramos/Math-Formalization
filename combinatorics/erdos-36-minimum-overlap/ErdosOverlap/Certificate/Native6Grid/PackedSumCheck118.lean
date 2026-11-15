module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows118
public import ErdosOverlap.Certificate.Native6Grid.PackedDots118

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0944_checked :
    packedSumCheck packedFactorsEven (row0944.map Prod.fst) evenDots0944 641 10 = true := by
  decide +kernel

theorem oddSum0944_checked :
    packedSumCheck packedFactorsOdd (row0944.map Prod.snd) oddDots0944 641 10 = true := by
  decide +kernel

theorem evenSum0945_checked :
    packedSumCheck packedFactorsEven (row0945.map Prod.fst) evenDots0945 641 10 = true := by
  decide +kernel

theorem oddSum0945_checked :
    packedSumCheck packedFactorsOdd (row0945.map Prod.snd) oddDots0945 641 10 = true := by
  decide +kernel

theorem evenSum0946_checked :
    packedSumCheck packedFactorsEven (row0946.map Prod.fst) evenDots0946 641 10 = true := by
  decide +kernel

theorem oddSum0946_checked :
    packedSumCheck packedFactorsOdd (row0946.map Prod.snd) oddDots0946 641 10 = true := by
  decide +kernel

theorem evenSum0947_checked :
    packedSumCheck packedFactorsEven (row0947.map Prod.fst) evenDots0947 641 10 = true := by
  decide +kernel

theorem oddSum0947_checked :
    packedSumCheck packedFactorsOdd (row0947.map Prod.snd) oddDots0947 641 10 = true := by
  decide +kernel

theorem evenSum0948_checked :
    packedSumCheck packedFactorsEven (row0948.map Prod.fst) evenDots0948 641 10 = true := by
  decide +kernel

theorem oddSum0948_checked :
    packedSumCheck packedFactorsOdd (row0948.map Prod.snd) oddDots0948 641 10 = true := by
  decide +kernel

theorem evenSum0949_checked :
    packedSumCheck packedFactorsEven (row0949.map Prod.fst) evenDots0949 641 10 = true := by
  decide +kernel

theorem oddSum0949_checked :
    packedSumCheck packedFactorsOdd (row0949.map Prod.snd) oddDots0949 641 10 = true := by
  decide +kernel

theorem evenSum0950_checked :
    packedSumCheck packedFactorsEven (row0950.map Prod.fst) evenDots0950 641 10 = true := by
  decide +kernel

theorem oddSum0950_checked :
    packedSumCheck packedFactorsOdd (row0950.map Prod.snd) oddDots0950 641 10 = true := by
  decide +kernel

theorem evenSum0951_checked :
    packedSumCheck packedFactorsEven (row0951.map Prod.fst) evenDots0951 641 10 = true := by
  decide +kernel

theorem oddSum0951_checked :
    packedSumCheck packedFactorsOdd (row0951.map Prod.snd) oddDots0951 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
