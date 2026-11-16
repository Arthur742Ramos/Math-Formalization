module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows054
public import ErdosOverlap.Certificate.Native6Grid.Rows055

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0432 : transitionRowCheck seeds row0432 row0433 = true := by
  decide +kernel

theorem transition0433 : transitionRowCheck seeds row0433 row0434 = true := by
  decide +kernel

theorem transition0434 : transitionRowCheck seeds row0434 row0435 = true := by
  decide +kernel

theorem transition0435 : transitionRowCheck seeds row0435 row0436 = true := by
  decide +kernel

theorem transition0436 : transitionRowCheck seeds row0436 row0437 = true := by
  decide +kernel

theorem transition0437 : transitionRowCheck seeds row0437 row0438 = true := by
  decide +kernel

theorem transition0438 : transitionRowCheck seeds row0438 row0439 = true := by
  decide +kernel

theorem transition0439 : transitionRowCheck seeds row0439 row0440 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
