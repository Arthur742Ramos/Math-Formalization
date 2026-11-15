module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows057
public import ErdosOverlap.Certificate.Native6Grid.Rows058

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0456 : transitionRowCheck seeds row0456 row0457 = true := by
  decide +kernel

theorem transition0457 : transitionRowCheck seeds row0457 row0458 = true := by
  decide +kernel

theorem transition0458 : transitionRowCheck seeds row0458 row0459 = true := by
  decide +kernel

theorem transition0459 : transitionRowCheck seeds row0459 row0460 = true := by
  decide +kernel

theorem transition0460 : transitionRowCheck seeds row0460 row0461 = true := by
  decide +kernel

theorem transition0461 : transitionRowCheck seeds row0461 row0462 = true := by
  decide +kernel

theorem transition0462 : transitionRowCheck seeds row0462 row0463 = true := by
  decide +kernel

theorem transition0463 : transitionRowCheck seeds row0463 row0464 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
