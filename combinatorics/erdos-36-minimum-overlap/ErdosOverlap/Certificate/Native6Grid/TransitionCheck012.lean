module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows012
public import ErdosOverlap.Certificate.Native6Grid.Rows013

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0096 : transitionRowCheck seeds row0096 row0097 = true := by
  decide +kernel

theorem transition0097 : transitionRowCheck seeds row0097 row0098 = true := by
  decide +kernel

theorem transition0098 : transitionRowCheck seeds row0098 row0099 = true := by
  decide +kernel

theorem transition0099 : transitionRowCheck seeds row0099 row0100 = true := by
  decide +kernel

theorem transition0100 : transitionRowCheck seeds row0100 row0101 = true := by
  decide +kernel

theorem transition0101 : transitionRowCheck seeds row0101 row0102 = true := by
  decide +kernel

theorem transition0102 : transitionRowCheck seeds row0102 row0103 = true := by
  decide +kernel

theorem transition0103 : transitionRowCheck seeds row0103 row0104 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
