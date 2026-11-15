module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows093
public import ErdosOverlap.Certificate.Native6Grid.Rows094

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0744 : transitionRowCheck seeds row0744 row0745 = true := by
  decide +kernel

theorem transition0745 : transitionRowCheck seeds row0745 row0746 = true := by
  decide +kernel

theorem transition0746 : transitionRowCheck seeds row0746 row0747 = true := by
  decide +kernel

theorem transition0747 : transitionRowCheck seeds row0747 row0748 = true := by
  decide +kernel

theorem transition0748 : transitionRowCheck seeds row0748 row0749 = true := by
  decide +kernel

theorem transition0749 : transitionRowCheck seeds row0749 row0750 = true := by
  decide +kernel

theorem transition0750 : transitionRowCheck seeds row0750 row0751 = true := by
  decide +kernel

theorem transition0751 : transitionRowCheck seeds row0751 row0752 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
