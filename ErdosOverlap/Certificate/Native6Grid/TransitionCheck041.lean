module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows041
public import ErdosOverlap.Certificate.Native6Grid.Rows042

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0328 : transitionRowCheck seeds row0328 row0329 = true := by
  decide +kernel

theorem transition0329 : transitionRowCheck seeds row0329 row0330 = true := by
  decide +kernel

theorem transition0330 : transitionRowCheck seeds row0330 row0331 = true := by
  decide +kernel

theorem transition0331 : transitionRowCheck seeds row0331 row0332 = true := by
  decide +kernel

theorem transition0332 : transitionRowCheck seeds row0332 row0333 = true := by
  decide +kernel

theorem transition0333 : transitionRowCheck seeds row0333 row0334 = true := by
  decide +kernel

theorem transition0334 : transitionRowCheck seeds row0334 row0335 = true := by
  decide +kernel

theorem transition0335 : transitionRowCheck seeds row0335 row0336 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
