module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows002
public import ErdosOverlap.Certificate.Native6Grid.PackedDots002

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0016_checked :
    packedSumCheck packedFactorsEven (row0016.map Prod.fst) evenDots0016 641 10 = true := by
  decide +kernel

theorem oddSum0016_checked :
    packedSumCheck packedFactorsOdd (row0016.map Prod.snd) oddDots0016 641 10 = true := by
  decide +kernel

theorem evenSum0017_checked :
    packedSumCheck packedFactorsEven (row0017.map Prod.fst) evenDots0017 641 10 = true := by
  decide +kernel

theorem oddSum0017_checked :
    packedSumCheck packedFactorsOdd (row0017.map Prod.snd) oddDots0017 641 10 = true := by
  decide +kernel

theorem evenSum0018_checked :
    packedSumCheck packedFactorsEven (row0018.map Prod.fst) evenDots0018 641 10 = true := by
  decide +kernel

theorem oddSum0018_checked :
    packedSumCheck packedFactorsOdd (row0018.map Prod.snd) oddDots0018 641 10 = true := by
  decide +kernel

theorem evenSum0019_checked :
    packedSumCheck packedFactorsEven (row0019.map Prod.fst) evenDots0019 641 10 = true := by
  decide +kernel

theorem oddSum0019_checked :
    packedSumCheck packedFactorsOdd (row0019.map Prod.snd) oddDots0019 641 10 = true := by
  decide +kernel

theorem evenSum0020_checked :
    packedSumCheck packedFactorsEven (row0020.map Prod.fst) evenDots0020 641 10 = true := by
  decide +kernel

theorem oddSum0020_checked :
    packedSumCheck packedFactorsOdd (row0020.map Prod.snd) oddDots0020 641 10 = true := by
  decide +kernel

theorem evenSum0021_checked :
    packedSumCheck packedFactorsEven (row0021.map Prod.fst) evenDots0021 641 10 = true := by
  decide +kernel

theorem oddSum0021_checked :
    packedSumCheck packedFactorsOdd (row0021.map Prod.snd) oddDots0021 641 10 = true := by
  decide +kernel

theorem evenSum0022_checked :
    packedSumCheck packedFactorsEven (row0022.map Prod.fst) evenDots0022 641 10 = true := by
  decide +kernel

theorem oddSum0022_checked :
    packedSumCheck packedFactorsOdd (row0022.map Prod.snd) oddDots0022 641 10 = true := by
  decide +kernel

theorem evenSum0023_checked :
    packedSumCheck packedFactorsEven (row0023.map Prod.fst) evenDots0023 641 10 = true := by
  decide +kernel

theorem oddSum0023_checked :
    packedSumCheck packedFactorsOdd (row0023.map Prod.snd) oddDots0023 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
