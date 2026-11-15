module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows108
public import ErdosOverlap.Certificate.Native6Grid.PackedDots108

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0864_checked :
    packedSumCheck packedFactorsEven (row0864.map Prod.fst) evenDots0864 641 10 = true := by
  decide +kernel

theorem oddSum0864_checked :
    packedSumCheck packedFactorsOdd (row0864.map Prod.snd) oddDots0864 641 10 = true := by
  decide +kernel

theorem evenSum0865_checked :
    packedSumCheck packedFactorsEven (row0865.map Prod.fst) evenDots0865 641 10 = true := by
  decide +kernel

theorem oddSum0865_checked :
    packedSumCheck packedFactorsOdd (row0865.map Prod.snd) oddDots0865 641 10 = true := by
  decide +kernel

theorem evenSum0866_checked :
    packedSumCheck packedFactorsEven (row0866.map Prod.fst) evenDots0866 641 10 = true := by
  decide +kernel

theorem oddSum0866_checked :
    packedSumCheck packedFactorsOdd (row0866.map Prod.snd) oddDots0866 641 10 = true := by
  decide +kernel

theorem evenSum0867_checked :
    packedSumCheck packedFactorsEven (row0867.map Prod.fst) evenDots0867 641 10 = true := by
  decide +kernel

theorem oddSum0867_checked :
    packedSumCheck packedFactorsOdd (row0867.map Prod.snd) oddDots0867 641 10 = true := by
  decide +kernel

theorem evenSum0868_checked :
    packedSumCheck packedFactorsEven (row0868.map Prod.fst) evenDots0868 641 10 = true := by
  decide +kernel

theorem oddSum0868_checked :
    packedSumCheck packedFactorsOdd (row0868.map Prod.snd) oddDots0868 641 10 = true := by
  decide +kernel

theorem evenSum0869_checked :
    packedSumCheck packedFactorsEven (row0869.map Prod.fst) evenDots0869 641 10 = true := by
  decide +kernel

theorem oddSum0869_checked :
    packedSumCheck packedFactorsOdd (row0869.map Prod.snd) oddDots0869 641 10 = true := by
  decide +kernel

theorem evenSum0870_checked :
    packedSumCheck packedFactorsEven (row0870.map Prod.fst) evenDots0870 641 10 = true := by
  decide +kernel

theorem oddSum0870_checked :
    packedSumCheck packedFactorsOdd (row0870.map Prod.snd) oddDots0870 641 10 = true := by
  decide +kernel

theorem evenSum0871_checked :
    packedSumCheck packedFactorsEven (row0871.map Prod.fst) evenDots0871 641 10 = true := by
  decide +kernel

theorem oddSum0871_checked :
    packedSumCheck packedFactorsOdd (row0871.map Prod.snd) oddDots0871 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
