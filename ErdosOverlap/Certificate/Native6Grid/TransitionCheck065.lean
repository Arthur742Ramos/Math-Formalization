module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows065
public import ErdosOverlap.Certificate.Native6Grid.Rows066

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0520 : transitionRowCheck seeds row0520 row0521 = true := by
  decide +kernel

theorem transition0521 : transitionRowCheck seeds row0521 row0522 = true := by
  decide +kernel

theorem transition0522 : transitionRowCheck seeds row0522 row0523 = true := by
  decide +kernel

theorem transition0523 : transitionRowCheck seeds row0523 row0524 = true := by
  decide +kernel

theorem transition0524 : transitionRowCheck seeds row0524 row0525 = true := by
  decide +kernel

theorem transition0525 : transitionRowCheck seeds row0525 row0526 = true := by
  decide +kernel

theorem transition0526 : transitionRowCheck seeds row0526 row0527 = true := by
  decide +kernel

theorem transition0527 : transitionRowCheck seeds row0527 row0528 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
