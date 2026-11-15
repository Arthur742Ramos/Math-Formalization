module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows067
public import ErdosOverlap.Certificate.Native6Grid.Rows068

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0536 : transitionRowCheck seeds row0536 row0537 = true := by
  decide +kernel

theorem transition0537 : transitionRowCheck seeds row0537 row0538 = true := by
  decide +kernel

theorem transition0538 : transitionRowCheck seeds row0538 row0539 = true := by
  decide +kernel

theorem transition0539 : transitionRowCheck seeds row0539 row0540 = true := by
  decide +kernel

theorem transition0540 : transitionRowCheck seeds row0540 row0541 = true := by
  decide +kernel

theorem transition0541 : transitionRowCheck seeds row0541 row0542 = true := by
  decide +kernel

theorem transition0542 : transitionRowCheck seeds row0542 row0543 = true := by
  decide +kernel

theorem transition0543 : transitionRowCheck seeds row0543 row0544 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
