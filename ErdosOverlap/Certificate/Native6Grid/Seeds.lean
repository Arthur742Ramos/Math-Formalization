module

public import ErdosOverlap.Certificate.Native6Grid.Seeds00
public import ErdosOverlap.Certificate.Native6Grid.Seeds01
public import ErdosOverlap.Certificate.Native6Grid.Seeds02
public import ErdosOverlap.Certificate.Native6Grid.Seeds03
public import ErdosOverlap.Certificate.Native6Grid.Seeds04
public import ErdosOverlap.Certificate.Native6Grid.Seeds05
public import ErdosOverlap.Certificate.Native6Grid.Seeds06
public import ErdosOverlap.Certificate.Native6Grid.Seeds07
public import ErdosOverlap.Certificate.Native6Grid.Seeds08
public import ErdosOverlap.Certificate.Native6Grid.Seeds09
public import ErdosOverlap.Certificate.Native6Grid.Seeds10
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def seeds : List (CosineTerm × RotationSeed) := seeds00 ++ seeds01 ++ seeds02 ++ seeds03 ++ seeds04 ++ seeds05 ++ seeds06 ++ seeds07 ++ seeds08 ++ seeds09 ++ seeds10

theorem seeds_terms : seeds.map Prod.fst = Native6Trig.terms := by rfl
theorem seeds_length : seeds.length = 641 := by decide +kernel

end
end ErdosOverlap.Native6Grid
