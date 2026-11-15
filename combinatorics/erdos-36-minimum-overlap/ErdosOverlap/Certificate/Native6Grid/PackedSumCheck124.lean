module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows124
public import ErdosOverlap.Certificate.Native6Grid.PackedDots124

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0992_checked :
    packedSumCheck packedFactorsEven (row0992.map Prod.fst) evenDots0992 641 10 = true := by
  decide +kernel

theorem oddSum0992_checked :
    packedSumCheck packedFactorsOdd (row0992.map Prod.snd) oddDots0992 641 10 = true := by
  decide +kernel

theorem evenSum0993_checked :
    packedSumCheck packedFactorsEven (row0993.map Prod.fst) evenDots0993 641 10 = true := by
  decide +kernel

theorem oddSum0993_checked :
    packedSumCheck packedFactorsOdd (row0993.map Prod.snd) oddDots0993 641 10 = true := by
  decide +kernel

theorem evenSum0994_checked :
    packedSumCheck packedFactorsEven (row0994.map Prod.fst) evenDots0994 641 10 = true := by
  decide +kernel

theorem oddSum0994_checked :
    packedSumCheck packedFactorsOdd (row0994.map Prod.snd) oddDots0994 641 10 = true := by
  decide +kernel

theorem evenSum0995_checked :
    packedSumCheck packedFactorsEven (row0995.map Prod.fst) evenDots0995 641 10 = true := by
  decide +kernel

theorem oddSum0995_checked :
    packedSumCheck packedFactorsOdd (row0995.map Prod.snd) oddDots0995 641 10 = true := by
  decide +kernel

theorem evenSum0996_checked :
    packedSumCheck packedFactorsEven (row0996.map Prod.fst) evenDots0996 641 10 = true := by
  decide +kernel

theorem oddSum0996_checked :
    packedSumCheck packedFactorsOdd (row0996.map Prod.snd) oddDots0996 641 10 = true := by
  decide +kernel

theorem evenSum0997_checked :
    packedSumCheck packedFactorsEven (row0997.map Prod.fst) evenDots0997 641 10 = true := by
  decide +kernel

theorem oddSum0997_checked :
    packedSumCheck packedFactorsOdd (row0997.map Prod.snd) oddDots0997 641 10 = true := by
  decide +kernel

theorem evenSum0998_checked :
    packedSumCheck packedFactorsEven (row0998.map Prod.fst) evenDots0998 641 10 = true := by
  decide +kernel

theorem oddSum0998_checked :
    packedSumCheck packedFactorsOdd (row0998.map Prod.snd) oddDots0998 641 10 = true := by
  decide +kernel

theorem evenSum0999_checked :
    packedSumCheck packedFactorsEven (row0999.map Prod.fst) evenDots0999 641 10 = true := by
  decide +kernel

theorem oddSum0999_checked :
    packedSumCheck packedFactorsOdd (row0999.map Prod.snd) oddDots0999 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
