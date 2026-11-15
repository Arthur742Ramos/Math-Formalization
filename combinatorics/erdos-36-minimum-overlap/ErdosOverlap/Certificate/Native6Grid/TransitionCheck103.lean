module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows103
public import ErdosOverlap.Certificate.Native6Grid.Rows104

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0824 : transitionRowCheck seeds row0824 row0825 = true := by
  decide +kernel

theorem transition0825 : transitionRowCheck seeds row0825 row0826 = true := by
  decide +kernel

theorem transition0826 : transitionRowCheck seeds row0826 row0827 = true := by
  decide +kernel

theorem transition0827 : transitionRowCheck seeds row0827 row0828 = true := by
  decide +kernel

theorem transition0828 : transitionRowCheck seeds row0828 row0829 = true := by
  decide +kernel

theorem transition0829 : transitionRowCheck seeds row0829 row0830 = true := by
  decide +kernel

theorem transition0830 : transitionRowCheck seeds row0830 row0831 = true := by
  decide +kernel

theorem transition0831 : transitionRowCheck seeds row0831 row0832 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
