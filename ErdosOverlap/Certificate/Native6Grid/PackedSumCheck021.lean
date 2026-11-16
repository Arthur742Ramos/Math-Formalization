module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows021
public import ErdosOverlap.Certificate.Native6Grid.PackedDots021

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0168_checked :
    packedSumCheck packedFactorsEven (row0168.map Prod.fst) evenDots0168 641 10 = true := by
  decide +kernel

theorem oddSum0168_checked :
    packedSumCheck packedFactorsOdd (row0168.map Prod.snd) oddDots0168 641 10 = true := by
  decide +kernel

theorem evenSum0169_checked :
    packedSumCheck packedFactorsEven (row0169.map Prod.fst) evenDots0169 641 10 = true := by
  decide +kernel

theorem oddSum0169_checked :
    packedSumCheck packedFactorsOdd (row0169.map Prod.snd) oddDots0169 641 10 = true := by
  decide +kernel

theorem evenSum0170_checked :
    packedSumCheck packedFactorsEven (row0170.map Prod.fst) evenDots0170 641 10 = true := by
  decide +kernel

theorem oddSum0170_checked :
    packedSumCheck packedFactorsOdd (row0170.map Prod.snd) oddDots0170 641 10 = true := by
  decide +kernel

theorem evenSum0171_checked :
    packedSumCheck packedFactorsEven (row0171.map Prod.fst) evenDots0171 641 10 = true := by
  decide +kernel

theorem oddSum0171_checked :
    packedSumCheck packedFactorsOdd (row0171.map Prod.snd) oddDots0171 641 10 = true := by
  decide +kernel

theorem evenSum0172_checked :
    packedSumCheck packedFactorsEven (row0172.map Prod.fst) evenDots0172 641 10 = true := by
  decide +kernel

theorem oddSum0172_checked :
    packedSumCheck packedFactorsOdd (row0172.map Prod.snd) oddDots0172 641 10 = true := by
  decide +kernel

theorem evenSum0173_checked :
    packedSumCheck packedFactorsEven (row0173.map Prod.fst) evenDots0173 641 10 = true := by
  decide +kernel

theorem oddSum0173_checked :
    packedSumCheck packedFactorsOdd (row0173.map Prod.snd) oddDots0173 641 10 = true := by
  decide +kernel

theorem evenSum0174_checked :
    packedSumCheck packedFactorsEven (row0174.map Prod.fst) evenDots0174 641 10 = true := by
  decide +kernel

theorem oddSum0174_checked :
    packedSumCheck packedFactorsOdd (row0174.map Prod.snd) oddDots0174 641 10 = true := by
  decide +kernel

theorem evenSum0175_checked :
    packedSumCheck packedFactorsEven (row0175.map Prod.fst) evenDots0175 641 10 = true := by
  decide +kernel

theorem oddSum0175_checked :
    packedSumCheck packedFactorsOdd (row0175.map Prod.snd) oddDots0175 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
