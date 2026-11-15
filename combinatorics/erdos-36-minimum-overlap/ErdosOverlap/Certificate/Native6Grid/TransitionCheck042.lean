module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows042
public import ErdosOverlap.Certificate.Native6Grid.Rows043

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0336 : transitionRowCheck seeds row0336 row0337 = true := by
  decide +kernel

theorem transition0337 : transitionRowCheck seeds row0337 row0338 = true := by
  decide +kernel

theorem transition0338 : transitionRowCheck seeds row0338 row0339 = true := by
  decide +kernel

theorem transition0339 : transitionRowCheck seeds row0339 row0340 = true := by
  decide +kernel

theorem transition0340 : transitionRowCheck seeds row0340 row0341 = true := by
  decide +kernel

theorem transition0341 : transitionRowCheck seeds row0341 row0342 = true := by
  decide +kernel

theorem transition0342 : transitionRowCheck seeds row0342 row0343 = true := by
  decide +kernel

theorem transition0343 : transitionRowCheck seeds row0343 row0344 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
