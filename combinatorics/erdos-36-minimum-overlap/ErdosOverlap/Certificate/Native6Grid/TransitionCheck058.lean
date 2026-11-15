module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows058
public import ErdosOverlap.Certificate.Native6Grid.Rows059

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0464 : transitionRowCheck seeds row0464 row0465 = true := by
  decide +kernel

theorem transition0465 : transitionRowCheck seeds row0465 row0466 = true := by
  decide +kernel

theorem transition0466 : transitionRowCheck seeds row0466 row0467 = true := by
  decide +kernel

theorem transition0467 : transitionRowCheck seeds row0467 row0468 = true := by
  decide +kernel

theorem transition0468 : transitionRowCheck seeds row0468 row0469 = true := by
  decide +kernel

theorem transition0469 : transitionRowCheck seeds row0469 row0470 = true := by
  decide +kernel

theorem transition0470 : transitionRowCheck seeds row0470 row0471 = true := by
  decide +kernel

theorem transition0471 : transitionRowCheck seeds row0471 row0472 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
