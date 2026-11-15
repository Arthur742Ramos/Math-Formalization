module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows036
public import ErdosOverlap.Certificate.Native6Grid.Rows037

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0288 : transitionRowCheck seeds row0288 row0289 = true := by
  decide +kernel

theorem transition0289 : transitionRowCheck seeds row0289 row0290 = true := by
  decide +kernel

theorem transition0290 : transitionRowCheck seeds row0290 row0291 = true := by
  decide +kernel

theorem transition0291 : transitionRowCheck seeds row0291 row0292 = true := by
  decide +kernel

theorem transition0292 : transitionRowCheck seeds row0292 row0293 = true := by
  decide +kernel

theorem transition0293 : transitionRowCheck seeds row0293 row0294 = true := by
  decide +kernel

theorem transition0294 : transitionRowCheck seeds row0294 row0295 = true := by
  decide +kernel

theorem transition0295 : transitionRowCheck seeds row0295 row0296 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
