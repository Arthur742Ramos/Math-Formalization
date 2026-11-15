module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows053
public import ErdosOverlap.Certificate.Native6Grid.Rows054

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0424 : transitionRowCheck seeds row0424 row0425 = true := by
  decide +kernel

theorem transition0425 : transitionRowCheck seeds row0425 row0426 = true := by
  decide +kernel

theorem transition0426 : transitionRowCheck seeds row0426 row0427 = true := by
  decide +kernel

theorem transition0427 : transitionRowCheck seeds row0427 row0428 = true := by
  decide +kernel

theorem transition0428 : transitionRowCheck seeds row0428 row0429 = true := by
  decide +kernel

theorem transition0429 : transitionRowCheck seeds row0429 row0430 = true := by
  decide +kernel

theorem transition0430 : transitionRowCheck seeds row0430 row0431 = true := by
  decide +kernel

theorem transition0431 : transitionRowCheck seeds row0431 row0432 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
