module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows047
public import ErdosOverlap.Certificate.Native6Grid.Rows048

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0376 : transitionRowCheck seeds row0376 row0377 = true := by
  decide +kernel

theorem transition0377 : transitionRowCheck seeds row0377 row0378 = true := by
  decide +kernel

theorem transition0378 : transitionRowCheck seeds row0378 row0379 = true := by
  decide +kernel

theorem transition0379 : transitionRowCheck seeds row0379 row0380 = true := by
  decide +kernel

theorem transition0380 : transitionRowCheck seeds row0380 row0381 = true := by
  decide +kernel

theorem transition0381 : transitionRowCheck seeds row0381 row0382 = true := by
  decide +kernel

theorem transition0382 : transitionRowCheck seeds row0382 row0383 = true := by
  decide +kernel

theorem transition0383 : transitionRowCheck seeds row0383 row0384 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
