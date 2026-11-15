module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows095
public import ErdosOverlap.Certificate.Native6Grid.Rows096

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0760 : transitionRowCheck seeds row0760 row0761 = true := by
  decide +kernel

theorem transition0761 : transitionRowCheck seeds row0761 row0762 = true := by
  decide +kernel

theorem transition0762 : transitionRowCheck seeds row0762 row0763 = true := by
  decide +kernel

theorem transition0763 : transitionRowCheck seeds row0763 row0764 = true := by
  decide +kernel

theorem transition0764 : transitionRowCheck seeds row0764 row0765 = true := by
  decide +kernel

theorem transition0765 : transitionRowCheck seeds row0765 row0766 = true := by
  decide +kernel

theorem transition0766 : transitionRowCheck seeds row0766 row0767 = true := by
  decide +kernel

theorem transition0767 : transitionRowCheck seeds row0767 row0768 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
