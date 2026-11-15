module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows072
public import ErdosOverlap.Certificate.Native6Grid.Rows073

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0576 : transitionRowCheck seeds row0576 row0577 = true := by
  decide +kernel

theorem transition0577 : transitionRowCheck seeds row0577 row0578 = true := by
  decide +kernel

theorem transition0578 : transitionRowCheck seeds row0578 row0579 = true := by
  decide +kernel

theorem transition0579 : transitionRowCheck seeds row0579 row0580 = true := by
  decide +kernel

theorem transition0580 : transitionRowCheck seeds row0580 row0581 = true := by
  decide +kernel

theorem transition0581 : transitionRowCheck seeds row0581 row0582 = true := by
  decide +kernel

theorem transition0582 : transitionRowCheck seeds row0582 row0583 = true := by
  decide +kernel

theorem transition0583 : transitionRowCheck seeds row0583 row0584 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
