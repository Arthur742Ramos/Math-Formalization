module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows097
public import ErdosOverlap.Certificate.Native6Grid.PackedDots097

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0776_checked :
    packedSumCheck packedFactorsEven (row0776.map Prod.fst) evenDots0776 641 10 = true := by
  decide +kernel

theorem oddSum0776_checked :
    packedSumCheck packedFactorsOdd (row0776.map Prod.snd) oddDots0776 641 10 = true := by
  decide +kernel

theorem evenSum0777_checked :
    packedSumCheck packedFactorsEven (row0777.map Prod.fst) evenDots0777 641 10 = true := by
  decide +kernel

theorem oddSum0777_checked :
    packedSumCheck packedFactorsOdd (row0777.map Prod.snd) oddDots0777 641 10 = true := by
  decide +kernel

theorem evenSum0778_checked :
    packedSumCheck packedFactorsEven (row0778.map Prod.fst) evenDots0778 641 10 = true := by
  decide +kernel

theorem oddSum0778_checked :
    packedSumCheck packedFactorsOdd (row0778.map Prod.snd) oddDots0778 641 10 = true := by
  decide +kernel

theorem evenSum0779_checked :
    packedSumCheck packedFactorsEven (row0779.map Prod.fst) evenDots0779 641 10 = true := by
  decide +kernel

theorem oddSum0779_checked :
    packedSumCheck packedFactorsOdd (row0779.map Prod.snd) oddDots0779 641 10 = true := by
  decide +kernel

theorem evenSum0780_checked :
    packedSumCheck packedFactorsEven (row0780.map Prod.fst) evenDots0780 641 10 = true := by
  decide +kernel

theorem oddSum0780_checked :
    packedSumCheck packedFactorsOdd (row0780.map Prod.snd) oddDots0780 641 10 = true := by
  decide +kernel

theorem evenSum0781_checked :
    packedSumCheck packedFactorsEven (row0781.map Prod.fst) evenDots0781 641 10 = true := by
  decide +kernel

theorem oddSum0781_checked :
    packedSumCheck packedFactorsOdd (row0781.map Prod.snd) oddDots0781 641 10 = true := by
  decide +kernel

theorem evenSum0782_checked :
    packedSumCheck packedFactorsEven (row0782.map Prod.fst) evenDots0782 641 10 = true := by
  decide +kernel

theorem oddSum0782_checked :
    packedSumCheck packedFactorsOdd (row0782.map Prod.snd) oddDots0782 641 10 = true := by
  decide +kernel

theorem evenSum0783_checked :
    packedSumCheck packedFactorsEven (row0783.map Prod.fst) evenDots0783 641 10 = true := by
  decide +kernel

theorem oddSum0783_checked :
    packedSumCheck packedFactorsOdd (row0783.map Prod.snd) oddDots0783 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
