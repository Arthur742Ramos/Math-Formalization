module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows043
public import ErdosOverlap.Certificate.Native6Grid.Rows044

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0344 : transitionRowCheck seeds row0344 row0345 = true := by
  decide +kernel

theorem transition0345 : transitionRowCheck seeds row0345 row0346 = true := by
  decide +kernel

theorem transition0346 : transitionRowCheck seeds row0346 row0347 = true := by
  decide +kernel

theorem transition0347 : transitionRowCheck seeds row0347 row0348 = true := by
  decide +kernel

theorem transition0348 : transitionRowCheck seeds row0348 row0349 = true := by
  decide +kernel

theorem transition0349 : transitionRowCheck seeds row0349 row0350 = true := by
  decide +kernel

theorem transition0350 : transitionRowCheck seeds row0350 row0351 = true := by
  decide +kernel

theorem transition0351 : transitionRowCheck seeds row0351 row0352 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
