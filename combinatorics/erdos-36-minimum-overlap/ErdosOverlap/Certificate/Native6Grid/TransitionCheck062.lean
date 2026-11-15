module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows062
public import ErdosOverlap.Certificate.Native6Grid.Rows063

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0496 : transitionRowCheck seeds row0496 row0497 = true := by
  decide +kernel

theorem transition0497 : transitionRowCheck seeds row0497 row0498 = true := by
  decide +kernel

theorem transition0498 : transitionRowCheck seeds row0498 row0499 = true := by
  decide +kernel

theorem transition0499 : transitionRowCheck seeds row0499 row0500 = true := by
  decide +kernel

theorem transition0500 : transitionRowCheck seeds row0500 row0501 = true := by
  decide +kernel

theorem transition0501 : transitionRowCheck seeds row0501 row0502 = true := by
  decide +kernel

theorem transition0502 : transitionRowCheck seeds row0502 row0503 = true := by
  decide +kernel

theorem transition0503 : transitionRowCheck seeds row0503 row0504 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
