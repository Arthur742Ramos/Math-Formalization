module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows079
public import ErdosOverlap.Certificate.Native6Grid.Rows080

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0632 : transitionRowCheck seeds row0632 row0633 = true := by
  decide +kernel

theorem transition0633 : transitionRowCheck seeds row0633 row0634 = true := by
  decide +kernel

theorem transition0634 : transitionRowCheck seeds row0634 row0635 = true := by
  decide +kernel

theorem transition0635 : transitionRowCheck seeds row0635 row0636 = true := by
  decide +kernel

theorem transition0636 : transitionRowCheck seeds row0636 row0637 = true := by
  decide +kernel

theorem transition0637 : transitionRowCheck seeds row0637 row0638 = true := by
  decide +kernel

theorem transition0638 : transitionRowCheck seeds row0638 row0639 = true := by
  decide +kernel

theorem transition0639 : transitionRowCheck seeds row0639 row0640 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
