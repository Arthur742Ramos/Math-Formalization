module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows104
public import ErdosOverlap.Certificate.Native6Grid.Rows105

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0832 : transitionRowCheck seeds row0832 row0833 = true := by
  decide +kernel

theorem transition0833 : transitionRowCheck seeds row0833 row0834 = true := by
  decide +kernel

theorem transition0834 : transitionRowCheck seeds row0834 row0835 = true := by
  decide +kernel

theorem transition0835 : transitionRowCheck seeds row0835 row0836 = true := by
  decide +kernel

theorem transition0836 : transitionRowCheck seeds row0836 row0837 = true := by
  decide +kernel

theorem transition0837 : transitionRowCheck seeds row0837 row0838 = true := by
  decide +kernel

theorem transition0838 : transitionRowCheck seeds row0838 row0839 = true := by
  decide +kernel

theorem transition0839 : transitionRowCheck seeds row0839 row0840 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
