module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows110
public import ErdosOverlap.Certificate.Native6Grid.PackedDots110

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0880_checked :
    packedSumCheck packedFactorsEven (row0880.map Prod.fst) evenDots0880 641 10 = true := by
  decide +kernel

theorem oddSum0880_checked :
    packedSumCheck packedFactorsOdd (row0880.map Prod.snd) oddDots0880 641 10 = true := by
  decide +kernel

theorem evenSum0881_checked :
    packedSumCheck packedFactorsEven (row0881.map Prod.fst) evenDots0881 641 10 = true := by
  decide +kernel

theorem oddSum0881_checked :
    packedSumCheck packedFactorsOdd (row0881.map Prod.snd) oddDots0881 641 10 = true := by
  decide +kernel

theorem evenSum0882_checked :
    packedSumCheck packedFactorsEven (row0882.map Prod.fst) evenDots0882 641 10 = true := by
  decide +kernel

theorem oddSum0882_checked :
    packedSumCheck packedFactorsOdd (row0882.map Prod.snd) oddDots0882 641 10 = true := by
  decide +kernel

theorem evenSum0883_checked :
    packedSumCheck packedFactorsEven (row0883.map Prod.fst) evenDots0883 641 10 = true := by
  decide +kernel

theorem oddSum0883_checked :
    packedSumCheck packedFactorsOdd (row0883.map Prod.snd) oddDots0883 641 10 = true := by
  decide +kernel

theorem evenSum0884_checked :
    packedSumCheck packedFactorsEven (row0884.map Prod.fst) evenDots0884 641 10 = true := by
  decide +kernel

theorem oddSum0884_checked :
    packedSumCheck packedFactorsOdd (row0884.map Prod.snd) oddDots0884 641 10 = true := by
  decide +kernel

theorem evenSum0885_checked :
    packedSumCheck packedFactorsEven (row0885.map Prod.fst) evenDots0885 641 10 = true := by
  decide +kernel

theorem oddSum0885_checked :
    packedSumCheck packedFactorsOdd (row0885.map Prod.snd) oddDots0885 641 10 = true := by
  decide +kernel

theorem evenSum0886_checked :
    packedSumCheck packedFactorsEven (row0886.map Prod.fst) evenDots0886 641 10 = true := by
  decide +kernel

theorem oddSum0886_checked :
    packedSumCheck packedFactorsOdd (row0886.map Prod.snd) oddDots0886 641 10 = true := by
  decide +kernel

theorem evenSum0887_checked :
    packedSumCheck packedFactorsEven (row0887.map Prod.fst) evenDots0887 641 10 = true := by
  decide +kernel

theorem oddSum0887_checked :
    packedSumCheck packedFactorsOdd (row0887.map Prod.snd) oddDots0887 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
