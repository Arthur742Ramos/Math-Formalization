module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows076
public import ErdosOverlap.Certificate.Native6Grid.Rows077

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0608 : transitionRowCheck seeds row0608 row0609 = true := by
  decide +kernel

theorem transition0609 : transitionRowCheck seeds row0609 row0610 = true := by
  decide +kernel

theorem transition0610 : transitionRowCheck seeds row0610 row0611 = true := by
  decide +kernel

theorem transition0611 : transitionRowCheck seeds row0611 row0612 = true := by
  decide +kernel

theorem transition0612 : transitionRowCheck seeds row0612 row0613 = true := by
  decide +kernel

theorem transition0613 : transitionRowCheck seeds row0613 row0614 = true := by
  decide +kernel

theorem transition0614 : transitionRowCheck seeds row0614 row0615 = true := by
  decide +kernel

theorem transition0615 : transitionRowCheck seeds row0615 row0616 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
