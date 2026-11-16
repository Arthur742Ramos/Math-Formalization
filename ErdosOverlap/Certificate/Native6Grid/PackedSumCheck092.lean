module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows092
public import ErdosOverlap.Certificate.Native6Grid.PackedDots092

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0736_checked :
    packedSumCheck packedFactorsEven (row0736.map Prod.fst) evenDots0736 641 10 = true := by
  decide +kernel

theorem oddSum0736_checked :
    packedSumCheck packedFactorsOdd (row0736.map Prod.snd) oddDots0736 641 10 = true := by
  decide +kernel

theorem evenSum0737_checked :
    packedSumCheck packedFactorsEven (row0737.map Prod.fst) evenDots0737 641 10 = true := by
  decide +kernel

theorem oddSum0737_checked :
    packedSumCheck packedFactorsOdd (row0737.map Prod.snd) oddDots0737 641 10 = true := by
  decide +kernel

theorem evenSum0738_checked :
    packedSumCheck packedFactorsEven (row0738.map Prod.fst) evenDots0738 641 10 = true := by
  decide +kernel

theorem oddSum0738_checked :
    packedSumCheck packedFactorsOdd (row0738.map Prod.snd) oddDots0738 641 10 = true := by
  decide +kernel

theorem evenSum0739_checked :
    packedSumCheck packedFactorsEven (row0739.map Prod.fst) evenDots0739 641 10 = true := by
  decide +kernel

theorem oddSum0739_checked :
    packedSumCheck packedFactorsOdd (row0739.map Prod.snd) oddDots0739 641 10 = true := by
  decide +kernel

theorem evenSum0740_checked :
    packedSumCheck packedFactorsEven (row0740.map Prod.fst) evenDots0740 641 10 = true := by
  decide +kernel

theorem oddSum0740_checked :
    packedSumCheck packedFactorsOdd (row0740.map Prod.snd) oddDots0740 641 10 = true := by
  decide +kernel

theorem evenSum0741_checked :
    packedSumCheck packedFactorsEven (row0741.map Prod.fst) evenDots0741 641 10 = true := by
  decide +kernel

theorem oddSum0741_checked :
    packedSumCheck packedFactorsOdd (row0741.map Prod.snd) oddDots0741 641 10 = true := by
  decide +kernel

theorem evenSum0742_checked :
    packedSumCheck packedFactorsEven (row0742.map Prod.fst) evenDots0742 641 10 = true := by
  decide +kernel

theorem oddSum0742_checked :
    packedSumCheck packedFactorsOdd (row0742.map Prod.snd) oddDots0742 641 10 = true := by
  decide +kernel

theorem evenSum0743_checked :
    packedSumCheck packedFactorsEven (row0743.map Prod.fst) evenDots0743 641 10 = true := by
  decide +kernel

theorem oddSum0743_checked :
    packedSumCheck packedFactorsOdd (row0743.map Prod.snd) oddDots0743 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
