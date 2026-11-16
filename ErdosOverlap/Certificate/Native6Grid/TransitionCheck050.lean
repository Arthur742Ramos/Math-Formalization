module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows050
public import ErdosOverlap.Certificate.Native6Grid.Rows051

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0400 : transitionRowCheck seeds row0400 row0401 = true := by
  decide +kernel

theorem transition0401 : transitionRowCheck seeds row0401 row0402 = true := by
  decide +kernel

theorem transition0402 : transitionRowCheck seeds row0402 row0403 = true := by
  decide +kernel

theorem transition0403 : transitionRowCheck seeds row0403 row0404 = true := by
  decide +kernel

theorem transition0404 : transitionRowCheck seeds row0404 row0405 = true := by
  decide +kernel

theorem transition0405 : transitionRowCheck seeds row0405 row0406 = true := by
  decide +kernel

theorem transition0406 : transitionRowCheck seeds row0406 row0407 = true := by
  decide +kernel

theorem transition0407 : transitionRowCheck seeds row0407 row0408 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
