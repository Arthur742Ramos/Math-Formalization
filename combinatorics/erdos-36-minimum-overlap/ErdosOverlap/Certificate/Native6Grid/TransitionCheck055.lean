module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows055
public import ErdosOverlap.Certificate.Native6Grid.Rows056

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0440 : transitionRowCheck seeds row0440 row0441 = true := by
  decide +kernel

theorem transition0441 : transitionRowCheck seeds row0441 row0442 = true := by
  decide +kernel

theorem transition0442 : transitionRowCheck seeds row0442 row0443 = true := by
  decide +kernel

theorem transition0443 : transitionRowCheck seeds row0443 row0444 = true := by
  decide +kernel

theorem transition0444 : transitionRowCheck seeds row0444 row0445 = true := by
  decide +kernel

theorem transition0445 : transitionRowCheck seeds row0445 row0446 = true := by
  decide +kernel

theorem transition0446 : transitionRowCheck seeds row0446 row0447 = true := by
  decide +kernel

theorem transition0447 : transitionRowCheck seeds row0447 row0448 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
