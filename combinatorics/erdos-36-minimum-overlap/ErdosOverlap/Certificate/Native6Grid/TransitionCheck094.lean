module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows094
public import ErdosOverlap.Certificate.Native6Grid.Rows095

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0752 : transitionRowCheck seeds row0752 row0753 = true := by
  decide +kernel

theorem transition0753 : transitionRowCheck seeds row0753 row0754 = true := by
  decide +kernel

theorem transition0754 : transitionRowCheck seeds row0754 row0755 = true := by
  decide +kernel

theorem transition0755 : transitionRowCheck seeds row0755 row0756 = true := by
  decide +kernel

theorem transition0756 : transitionRowCheck seeds row0756 row0757 = true := by
  decide +kernel

theorem transition0757 : transitionRowCheck seeds row0757 row0758 = true := by
  decide +kernel

theorem transition0758 : transitionRowCheck seeds row0758 row0759 = true := by
  decide +kernel

theorem transition0759 : transitionRowCheck seeds row0759 row0760 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
