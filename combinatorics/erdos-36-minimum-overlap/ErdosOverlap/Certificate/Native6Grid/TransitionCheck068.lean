module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows068
public import ErdosOverlap.Certificate.Native6Grid.Rows069

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0544 : transitionRowCheck seeds row0544 row0545 = true := by
  decide +kernel

theorem transition0545 : transitionRowCheck seeds row0545 row0546 = true := by
  decide +kernel

theorem transition0546 : transitionRowCheck seeds row0546 row0547 = true := by
  decide +kernel

theorem transition0547 : transitionRowCheck seeds row0547 row0548 = true := by
  decide +kernel

theorem transition0548 : transitionRowCheck seeds row0548 row0549 = true := by
  decide +kernel

theorem transition0549 : transitionRowCheck seeds row0549 row0550 = true := by
  decide +kernel

theorem transition0550 : transitionRowCheck seeds row0550 row0551 = true := by
  decide +kernel

theorem transition0551 : transitionRowCheck seeds row0551 row0552 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
