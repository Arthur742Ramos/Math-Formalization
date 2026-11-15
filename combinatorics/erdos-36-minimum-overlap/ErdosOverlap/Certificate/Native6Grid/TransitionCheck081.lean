module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows081
public import ErdosOverlap.Certificate.Native6Grid.Rows082

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0648 : transitionRowCheck seeds row0648 row0649 = true := by
  decide +kernel

theorem transition0649 : transitionRowCheck seeds row0649 row0650 = true := by
  decide +kernel

theorem transition0650 : transitionRowCheck seeds row0650 row0651 = true := by
  decide +kernel

theorem transition0651 : transitionRowCheck seeds row0651 row0652 = true := by
  decide +kernel

theorem transition0652 : transitionRowCheck seeds row0652 row0653 = true := by
  decide +kernel

theorem transition0653 : transitionRowCheck seeds row0653 row0654 = true := by
  decide +kernel

theorem transition0654 : transitionRowCheck seeds row0654 row0655 = true := by
  decide +kernel

theorem transition0655 : transitionRowCheck seeds row0655 row0656 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
