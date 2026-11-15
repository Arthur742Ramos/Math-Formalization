module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows059
public import ErdosOverlap.Certificate.Native6Grid.Rows060

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0472 : transitionRowCheck seeds row0472 row0473 = true := by
  decide +kernel

theorem transition0473 : transitionRowCheck seeds row0473 row0474 = true := by
  decide +kernel

theorem transition0474 : transitionRowCheck seeds row0474 row0475 = true := by
  decide +kernel

theorem transition0475 : transitionRowCheck seeds row0475 row0476 = true := by
  decide +kernel

theorem transition0476 : transitionRowCheck seeds row0476 row0477 = true := by
  decide +kernel

theorem transition0477 : transitionRowCheck seeds row0477 row0478 = true := by
  decide +kernel

theorem transition0478 : transitionRowCheck seeds row0478 row0479 = true := by
  decide +kernel

theorem transition0479 : transitionRowCheck seeds row0479 row0480 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
