module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows049
public import ErdosOverlap.Certificate.Native6Grid.Rows050

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0392 : transitionRowCheck seeds row0392 row0393 = true := by
  decide +kernel

theorem transition0393 : transitionRowCheck seeds row0393 row0394 = true := by
  decide +kernel

theorem transition0394 : transitionRowCheck seeds row0394 row0395 = true := by
  decide +kernel

theorem transition0395 : transitionRowCheck seeds row0395 row0396 = true := by
  decide +kernel

theorem transition0396 : transitionRowCheck seeds row0396 row0397 = true := by
  decide +kernel

theorem transition0397 : transitionRowCheck seeds row0397 row0398 = true := by
  decide +kernel

theorem transition0398 : transitionRowCheck seeds row0398 row0399 = true := by
  decide +kernel

theorem transition0399 : transitionRowCheck seeds row0399 row0400 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
