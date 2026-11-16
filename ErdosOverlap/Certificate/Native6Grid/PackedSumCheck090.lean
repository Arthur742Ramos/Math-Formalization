module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows090
public import ErdosOverlap.Certificate.Native6Grid.PackedDots090

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0720_checked :
    packedSumCheck packedFactorsEven (row0720.map Prod.fst) evenDots0720 641 10 = true := by
  decide +kernel

theorem oddSum0720_checked :
    packedSumCheck packedFactorsOdd (row0720.map Prod.snd) oddDots0720 641 10 = true := by
  decide +kernel

theorem evenSum0721_checked :
    packedSumCheck packedFactorsEven (row0721.map Prod.fst) evenDots0721 641 10 = true := by
  decide +kernel

theorem oddSum0721_checked :
    packedSumCheck packedFactorsOdd (row0721.map Prod.snd) oddDots0721 641 10 = true := by
  decide +kernel

theorem evenSum0722_checked :
    packedSumCheck packedFactorsEven (row0722.map Prod.fst) evenDots0722 641 10 = true := by
  decide +kernel

theorem oddSum0722_checked :
    packedSumCheck packedFactorsOdd (row0722.map Prod.snd) oddDots0722 641 10 = true := by
  decide +kernel

theorem evenSum0723_checked :
    packedSumCheck packedFactorsEven (row0723.map Prod.fst) evenDots0723 641 10 = true := by
  decide +kernel

theorem oddSum0723_checked :
    packedSumCheck packedFactorsOdd (row0723.map Prod.snd) oddDots0723 641 10 = true := by
  decide +kernel

theorem evenSum0724_checked :
    packedSumCheck packedFactorsEven (row0724.map Prod.fst) evenDots0724 641 10 = true := by
  decide +kernel

theorem oddSum0724_checked :
    packedSumCheck packedFactorsOdd (row0724.map Prod.snd) oddDots0724 641 10 = true := by
  decide +kernel

theorem evenSum0725_checked :
    packedSumCheck packedFactorsEven (row0725.map Prod.fst) evenDots0725 641 10 = true := by
  decide +kernel

theorem oddSum0725_checked :
    packedSumCheck packedFactorsOdd (row0725.map Prod.snd) oddDots0725 641 10 = true := by
  decide +kernel

theorem evenSum0726_checked :
    packedSumCheck packedFactorsEven (row0726.map Prod.fst) evenDots0726 641 10 = true := by
  decide +kernel

theorem oddSum0726_checked :
    packedSumCheck packedFactorsOdd (row0726.map Prod.snd) oddDots0726 641 10 = true := by
  decide +kernel

theorem evenSum0727_checked :
    packedSumCheck packedFactorsEven (row0727.map Prod.fst) evenDots0727 641 10 = true := by
  decide +kernel

theorem oddSum0727_checked :
    packedSumCheck packedFactorsOdd (row0727.map Prod.snd) oddDots0727 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
