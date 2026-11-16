module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows089
public import ErdosOverlap.Certificate.Native6Grid.PackedDots089

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0712_checked :
    packedSumCheck packedFactorsEven (row0712.map Prod.fst) evenDots0712 641 10 = true := by
  decide +kernel

theorem oddSum0712_checked :
    packedSumCheck packedFactorsOdd (row0712.map Prod.snd) oddDots0712 641 10 = true := by
  decide +kernel

theorem evenSum0713_checked :
    packedSumCheck packedFactorsEven (row0713.map Prod.fst) evenDots0713 641 10 = true := by
  decide +kernel

theorem oddSum0713_checked :
    packedSumCheck packedFactorsOdd (row0713.map Prod.snd) oddDots0713 641 10 = true := by
  decide +kernel

theorem evenSum0714_checked :
    packedSumCheck packedFactorsEven (row0714.map Prod.fst) evenDots0714 641 10 = true := by
  decide +kernel

theorem oddSum0714_checked :
    packedSumCheck packedFactorsOdd (row0714.map Prod.snd) oddDots0714 641 10 = true := by
  decide +kernel

theorem evenSum0715_checked :
    packedSumCheck packedFactorsEven (row0715.map Prod.fst) evenDots0715 641 10 = true := by
  decide +kernel

theorem oddSum0715_checked :
    packedSumCheck packedFactorsOdd (row0715.map Prod.snd) oddDots0715 641 10 = true := by
  decide +kernel

theorem evenSum0716_checked :
    packedSumCheck packedFactorsEven (row0716.map Prod.fst) evenDots0716 641 10 = true := by
  decide +kernel

theorem oddSum0716_checked :
    packedSumCheck packedFactorsOdd (row0716.map Prod.snd) oddDots0716 641 10 = true := by
  decide +kernel

theorem evenSum0717_checked :
    packedSumCheck packedFactorsEven (row0717.map Prod.fst) evenDots0717 641 10 = true := by
  decide +kernel

theorem oddSum0717_checked :
    packedSumCheck packedFactorsOdd (row0717.map Prod.snd) oddDots0717 641 10 = true := by
  decide +kernel

theorem evenSum0718_checked :
    packedSumCheck packedFactorsEven (row0718.map Prod.fst) evenDots0718 641 10 = true := by
  decide +kernel

theorem oddSum0718_checked :
    packedSumCheck packedFactorsOdd (row0718.map Prod.snd) oddDots0718 641 10 = true := by
  decide +kernel

theorem evenSum0719_checked :
    packedSumCheck packedFactorsEven (row0719.map Prod.fst) evenDots0719 641 10 = true := by
  decide +kernel

theorem oddSum0719_checked :
    packedSumCheck packedFactorsOdd (row0719.map Prod.snd) oddDots0719 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
