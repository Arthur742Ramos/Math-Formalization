module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows105
public import ErdosOverlap.Certificate.Native6Grid.Rows106

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0840 : transitionRowCheck seeds row0840 row0841 = true := by
  decide +kernel

theorem transition0841 : transitionRowCheck seeds row0841 row0842 = true := by
  decide +kernel

theorem transition0842 : transitionRowCheck seeds row0842 row0843 = true := by
  decide +kernel

theorem transition0843 : transitionRowCheck seeds row0843 row0844 = true := by
  decide +kernel

theorem transition0844 : transitionRowCheck seeds row0844 row0845 = true := by
  decide +kernel

theorem transition0845 : transitionRowCheck seeds row0845 row0846 = true := by
  decide +kernel

theorem transition0846 : transitionRowCheck seeds row0846 row0847 = true := by
  decide +kernel

theorem transition0847 : transitionRowCheck seeds row0847 row0848 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
