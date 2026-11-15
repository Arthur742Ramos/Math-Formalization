module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows066
public import ErdosOverlap.Certificate.Native6Grid.Rows067

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0528 : transitionRowCheck seeds row0528 row0529 = true := by
  decide +kernel

theorem transition0529 : transitionRowCheck seeds row0529 row0530 = true := by
  decide +kernel

theorem transition0530 : transitionRowCheck seeds row0530 row0531 = true := by
  decide +kernel

theorem transition0531 : transitionRowCheck seeds row0531 row0532 = true := by
  decide +kernel

theorem transition0532 : transitionRowCheck seeds row0532 row0533 = true := by
  decide +kernel

theorem transition0533 : transitionRowCheck seeds row0533 row0534 = true := by
  decide +kernel

theorem transition0534 : transitionRowCheck seeds row0534 row0535 = true := by
  decide +kernel

theorem transition0535 : transitionRowCheck seeds row0535 row0536 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
