module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows111
public import ErdosOverlap.Certificate.Native6Grid.PackedDots111

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0888_checked :
    packedSumCheck packedFactorsEven (row0888.map Prod.fst) evenDots0888 641 10 = true := by
  decide +kernel

theorem oddSum0888_checked :
    packedSumCheck packedFactorsOdd (row0888.map Prod.snd) oddDots0888 641 10 = true := by
  decide +kernel

theorem evenSum0889_checked :
    packedSumCheck packedFactorsEven (row0889.map Prod.fst) evenDots0889 641 10 = true := by
  decide +kernel

theorem oddSum0889_checked :
    packedSumCheck packedFactorsOdd (row0889.map Prod.snd) oddDots0889 641 10 = true := by
  decide +kernel

theorem evenSum0890_checked :
    packedSumCheck packedFactorsEven (row0890.map Prod.fst) evenDots0890 641 10 = true := by
  decide +kernel

theorem oddSum0890_checked :
    packedSumCheck packedFactorsOdd (row0890.map Prod.snd) oddDots0890 641 10 = true := by
  decide +kernel

theorem evenSum0891_checked :
    packedSumCheck packedFactorsEven (row0891.map Prod.fst) evenDots0891 641 10 = true := by
  decide +kernel

theorem oddSum0891_checked :
    packedSumCheck packedFactorsOdd (row0891.map Prod.snd) oddDots0891 641 10 = true := by
  decide +kernel

theorem evenSum0892_checked :
    packedSumCheck packedFactorsEven (row0892.map Prod.fst) evenDots0892 641 10 = true := by
  decide +kernel

theorem oddSum0892_checked :
    packedSumCheck packedFactorsOdd (row0892.map Prod.snd) oddDots0892 641 10 = true := by
  decide +kernel

theorem evenSum0893_checked :
    packedSumCheck packedFactorsEven (row0893.map Prod.fst) evenDots0893 641 10 = true := by
  decide +kernel

theorem oddSum0893_checked :
    packedSumCheck packedFactorsOdd (row0893.map Prod.snd) oddDots0893 641 10 = true := by
  decide +kernel

theorem evenSum0894_checked :
    packedSumCheck packedFactorsEven (row0894.map Prod.fst) evenDots0894 641 10 = true := by
  decide +kernel

theorem oddSum0894_checked :
    packedSumCheck packedFactorsOdd (row0894.map Prod.snd) oddDots0894 641 10 = true := by
  decide +kernel

theorem evenSum0895_checked :
    packedSumCheck packedFactorsEven (row0895.map Prod.fst) evenDots0895 641 10 = true := by
  decide +kernel

theorem oddSum0895_checked :
    packedSumCheck packedFactorsOdd (row0895.map Prod.snd) oddDots0895 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
