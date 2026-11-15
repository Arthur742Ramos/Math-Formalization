module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows082
public import ErdosOverlap.Certificate.Native6Grid.Rows083

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0656 : transitionRowCheck seeds row0656 row0657 = true := by
  decide +kernel

theorem transition0657 : transitionRowCheck seeds row0657 row0658 = true := by
  decide +kernel

theorem transition0658 : transitionRowCheck seeds row0658 row0659 = true := by
  decide +kernel

theorem transition0659 : transitionRowCheck seeds row0659 row0660 = true := by
  decide +kernel

theorem transition0660 : transitionRowCheck seeds row0660 row0661 = true := by
  decide +kernel

theorem transition0661 : transitionRowCheck seeds row0661 row0662 = true := by
  decide +kernel

theorem transition0662 : transitionRowCheck seeds row0662 row0663 = true := by
  decide +kernel

theorem transition0663 : transitionRowCheck seeds row0663 row0664 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
