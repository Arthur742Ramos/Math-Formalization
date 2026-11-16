module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows051
public import ErdosOverlap.Certificate.Native6Grid.Rows052

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0408 : transitionRowCheck seeds row0408 row0409 = true := by
  decide +kernel

theorem transition0409 : transitionRowCheck seeds row0409 row0410 = true := by
  decide +kernel

theorem transition0410 : transitionRowCheck seeds row0410 row0411 = true := by
  decide +kernel

theorem transition0411 : transitionRowCheck seeds row0411 row0412 = true := by
  decide +kernel

theorem transition0412 : transitionRowCheck seeds row0412 row0413 = true := by
  decide +kernel

theorem transition0413 : transitionRowCheck seeds row0413 row0414 = true := by
  decide +kernel

theorem transition0414 : transitionRowCheck seeds row0414 row0415 = true := by
  decide +kernel

theorem transition0415 : transitionRowCheck seeds row0415 row0416 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
