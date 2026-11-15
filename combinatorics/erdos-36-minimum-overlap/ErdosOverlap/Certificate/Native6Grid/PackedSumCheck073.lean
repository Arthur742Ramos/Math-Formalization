module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows073
public import ErdosOverlap.Certificate.Native6Grid.PackedDots073

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0584_checked :
    packedSumCheck packedFactorsEven (row0584.map Prod.fst) evenDots0584 641 10 = true := by
  decide +kernel

theorem oddSum0584_checked :
    packedSumCheck packedFactorsOdd (row0584.map Prod.snd) oddDots0584 641 10 = true := by
  decide +kernel

theorem evenSum0585_checked :
    packedSumCheck packedFactorsEven (row0585.map Prod.fst) evenDots0585 641 10 = true := by
  decide +kernel

theorem oddSum0585_checked :
    packedSumCheck packedFactorsOdd (row0585.map Prod.snd) oddDots0585 641 10 = true := by
  decide +kernel

theorem evenSum0586_checked :
    packedSumCheck packedFactorsEven (row0586.map Prod.fst) evenDots0586 641 10 = true := by
  decide +kernel

theorem oddSum0586_checked :
    packedSumCheck packedFactorsOdd (row0586.map Prod.snd) oddDots0586 641 10 = true := by
  decide +kernel

theorem evenSum0587_checked :
    packedSumCheck packedFactorsEven (row0587.map Prod.fst) evenDots0587 641 10 = true := by
  decide +kernel

theorem oddSum0587_checked :
    packedSumCheck packedFactorsOdd (row0587.map Prod.snd) oddDots0587 641 10 = true := by
  decide +kernel

theorem evenSum0588_checked :
    packedSumCheck packedFactorsEven (row0588.map Prod.fst) evenDots0588 641 10 = true := by
  decide +kernel

theorem oddSum0588_checked :
    packedSumCheck packedFactorsOdd (row0588.map Prod.snd) oddDots0588 641 10 = true := by
  decide +kernel

theorem evenSum0589_checked :
    packedSumCheck packedFactorsEven (row0589.map Prod.fst) evenDots0589 641 10 = true := by
  decide +kernel

theorem oddSum0589_checked :
    packedSumCheck packedFactorsOdd (row0589.map Prod.snd) oddDots0589 641 10 = true := by
  decide +kernel

theorem evenSum0590_checked :
    packedSumCheck packedFactorsEven (row0590.map Prod.fst) evenDots0590 641 10 = true := by
  decide +kernel

theorem oddSum0590_checked :
    packedSumCheck packedFactorsOdd (row0590.map Prod.snd) oddDots0590 641 10 = true := by
  decide +kernel

theorem evenSum0591_checked :
    packedSumCheck packedFactorsEven (row0591.map Prod.fst) evenDots0591 641 10 = true := by
  decide +kernel

theorem oddSum0591_checked :
    packedSumCheck packedFactorsOdd (row0591.map Prod.snd) oddDots0591 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
