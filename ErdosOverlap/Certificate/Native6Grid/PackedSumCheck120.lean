module

public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsEven
public import ErdosOverlap.Certificate.Native6Grid.PackedFactorsOdd
public import ErdosOverlap.Certificate.Native6Grid.Rows120
public import ErdosOverlap.Certificate.Native6Grid.PackedDots120

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem evenSum0960_checked :
    packedSumCheck packedFactorsEven (row0960.map Prod.fst) evenDots0960 641 10 = true := by
  decide +kernel

theorem oddSum0960_checked :
    packedSumCheck packedFactorsOdd (row0960.map Prod.snd) oddDots0960 641 10 = true := by
  decide +kernel

theorem evenSum0961_checked :
    packedSumCheck packedFactorsEven (row0961.map Prod.fst) evenDots0961 641 10 = true := by
  decide +kernel

theorem oddSum0961_checked :
    packedSumCheck packedFactorsOdd (row0961.map Prod.snd) oddDots0961 641 10 = true := by
  decide +kernel

theorem evenSum0962_checked :
    packedSumCheck packedFactorsEven (row0962.map Prod.fst) evenDots0962 641 10 = true := by
  decide +kernel

theorem oddSum0962_checked :
    packedSumCheck packedFactorsOdd (row0962.map Prod.snd) oddDots0962 641 10 = true := by
  decide +kernel

theorem evenSum0963_checked :
    packedSumCheck packedFactorsEven (row0963.map Prod.fst) evenDots0963 641 10 = true := by
  decide +kernel

theorem oddSum0963_checked :
    packedSumCheck packedFactorsOdd (row0963.map Prod.snd) oddDots0963 641 10 = true := by
  decide +kernel

theorem evenSum0964_checked :
    packedSumCheck packedFactorsEven (row0964.map Prod.fst) evenDots0964 641 10 = true := by
  decide +kernel

theorem oddSum0964_checked :
    packedSumCheck packedFactorsOdd (row0964.map Prod.snd) oddDots0964 641 10 = true := by
  decide +kernel

theorem evenSum0965_checked :
    packedSumCheck packedFactorsEven (row0965.map Prod.fst) evenDots0965 641 10 = true := by
  decide +kernel

theorem oddSum0965_checked :
    packedSumCheck packedFactorsOdd (row0965.map Prod.snd) oddDots0965 641 10 = true := by
  decide +kernel

theorem evenSum0966_checked :
    packedSumCheck packedFactorsEven (row0966.map Prod.fst) evenDots0966 641 10 = true := by
  decide +kernel

theorem oddSum0966_checked :
    packedSumCheck packedFactorsOdd (row0966.map Prod.snd) oddDots0966 641 10 = true := by
  decide +kernel

theorem evenSum0967_checked :
    packedSumCheck packedFactorsEven (row0967.map Prod.fst) evenDots0967 641 10 = true := by
  decide +kernel

theorem oddSum0967_checked :
    packedSumCheck packedFactorsOdd (row0967.map Prod.snd) oddDots0967 641 10 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
