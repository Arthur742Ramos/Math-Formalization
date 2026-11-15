module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows071
public import ErdosOverlap.Certificate.Native6Grid.Rows072

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0568 : transitionRowCheck seeds row0568 row0569 = true := by
  decide +kernel

theorem transition0569 : transitionRowCheck seeds row0569 row0570 = true := by
  decide +kernel

theorem transition0570 : transitionRowCheck seeds row0570 row0571 = true := by
  decide +kernel

theorem transition0571 : transitionRowCheck seeds row0571 row0572 = true := by
  decide +kernel

theorem transition0572 : transitionRowCheck seeds row0572 row0573 = true := by
  decide +kernel

theorem transition0573 : transitionRowCheck seeds row0573 row0574 = true := by
  decide +kernel

theorem transition0574 : transitionRowCheck seeds row0574 row0575 = true := by
  decide +kernel

theorem transition0575 : transitionRowCheck seeds row0575 row0576 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
