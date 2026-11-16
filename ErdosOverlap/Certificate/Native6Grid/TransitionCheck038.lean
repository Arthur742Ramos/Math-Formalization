module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows038
public import ErdosOverlap.Certificate.Native6Grid.Rows039

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0304 : transitionRowCheck seeds row0304 row0305 = true := by
  decide +kernel

theorem transition0305 : transitionRowCheck seeds row0305 row0306 = true := by
  decide +kernel

theorem transition0306 : transitionRowCheck seeds row0306 row0307 = true := by
  decide +kernel

theorem transition0307 : transitionRowCheck seeds row0307 row0308 = true := by
  decide +kernel

theorem transition0308 : transitionRowCheck seeds row0308 row0309 = true := by
  decide +kernel

theorem transition0309 : transitionRowCheck seeds row0309 row0310 = true := by
  decide +kernel

theorem transition0310 : transitionRowCheck seeds row0310 row0311 = true := by
  decide +kernel

theorem transition0311 : transitionRowCheck seeds row0311 row0312 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
