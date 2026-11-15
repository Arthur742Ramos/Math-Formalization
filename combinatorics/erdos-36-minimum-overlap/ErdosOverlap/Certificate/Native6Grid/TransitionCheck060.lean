module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows060
public import ErdosOverlap.Certificate.Native6Grid.Rows061

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0480 : transitionRowCheck seeds row0480 row0481 = true := by
  decide +kernel

theorem transition0481 : transitionRowCheck seeds row0481 row0482 = true := by
  decide +kernel

theorem transition0482 : transitionRowCheck seeds row0482 row0483 = true := by
  decide +kernel

theorem transition0483 : transitionRowCheck seeds row0483 row0484 = true := by
  decide +kernel

theorem transition0484 : transitionRowCheck seeds row0484 row0485 = true := by
  decide +kernel

theorem transition0485 : transitionRowCheck seeds row0485 row0486 = true := by
  decide +kernel

theorem transition0486 : transitionRowCheck seeds row0486 row0487 = true := by
  decide +kernel

theorem transition0487 : transitionRowCheck seeds row0487 row0488 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
