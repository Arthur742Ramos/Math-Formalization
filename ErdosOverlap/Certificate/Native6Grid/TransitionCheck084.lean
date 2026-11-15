module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows084
public import ErdosOverlap.Certificate.Native6Grid.Rows085

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0672 : transitionRowCheck seeds row0672 row0673 = true := by
  decide +kernel

theorem transition0673 : transitionRowCheck seeds row0673 row0674 = true := by
  decide +kernel

theorem transition0674 : transitionRowCheck seeds row0674 row0675 = true := by
  decide +kernel

theorem transition0675 : transitionRowCheck seeds row0675 row0676 = true := by
  decide +kernel

theorem transition0676 : transitionRowCheck seeds row0676 row0677 = true := by
  decide +kernel

theorem transition0677 : transitionRowCheck seeds row0677 row0678 = true := by
  decide +kernel

theorem transition0678 : transitionRowCheck seeds row0678 row0679 = true := by
  decide +kernel

theorem transition0679 : transitionRowCheck seeds row0679 row0680 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
