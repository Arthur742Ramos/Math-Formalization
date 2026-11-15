module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows013
public import ErdosOverlap.Certificate.Native6Grid.Rows014

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0104 : transitionRowCheck seeds row0104 row0105 = true := by
  decide +kernel

theorem transition0105 : transitionRowCheck seeds row0105 row0106 = true := by
  decide +kernel

theorem transition0106 : transitionRowCheck seeds row0106 row0107 = true := by
  decide +kernel

theorem transition0107 : transitionRowCheck seeds row0107 row0108 = true := by
  decide +kernel

theorem transition0108 : transitionRowCheck seeds row0108 row0109 = true := by
  decide +kernel

theorem transition0109 : transitionRowCheck seeds row0109 row0110 = true := by
  decide +kernel

theorem transition0110 : transitionRowCheck seeds row0110 row0111 = true := by
  decide +kernel

theorem transition0111 : transitionRowCheck seeds row0111 row0112 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
