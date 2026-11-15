module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows061
public import ErdosOverlap.Certificate.Native6Grid.Rows062

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0488 : transitionRowCheck seeds row0488 row0489 = true := by
  decide +kernel

theorem transition0489 : transitionRowCheck seeds row0489 row0490 = true := by
  decide +kernel

theorem transition0490 : transitionRowCheck seeds row0490 row0491 = true := by
  decide +kernel

theorem transition0491 : transitionRowCheck seeds row0491 row0492 = true := by
  decide +kernel

theorem transition0492 : transitionRowCheck seeds row0492 row0493 = true := by
  decide +kernel

theorem transition0493 : transitionRowCheck seeds row0493 row0494 = true := by
  decide +kernel

theorem transition0494 : transitionRowCheck seeds row0494 row0495 = true := by
  decide +kernel

theorem transition0495 : transitionRowCheck seeds row0495 row0496 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
