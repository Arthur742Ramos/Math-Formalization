module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows056
public import ErdosOverlap.Certificate.Native6Grid.Rows057

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0448 : transitionRowCheck seeds row0448 row0449 = true := by
  decide +kernel

theorem transition0449 : transitionRowCheck seeds row0449 row0450 = true := by
  decide +kernel

theorem transition0450 : transitionRowCheck seeds row0450 row0451 = true := by
  decide +kernel

theorem transition0451 : transitionRowCheck seeds row0451 row0452 = true := by
  decide +kernel

theorem transition0452 : transitionRowCheck seeds row0452 row0453 = true := by
  decide +kernel

theorem transition0453 : transitionRowCheck seeds row0453 row0454 = true := by
  decide +kernel

theorem transition0454 : transitionRowCheck seeds row0454 row0455 = true := by
  decide +kernel

theorem transition0455 : transitionRowCheck seeds row0455 row0456 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
