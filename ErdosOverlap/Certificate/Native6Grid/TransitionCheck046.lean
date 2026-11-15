module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows046
public import ErdosOverlap.Certificate.Native6Grid.Rows047

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0368 : transitionRowCheck seeds row0368 row0369 = true := by
  decide +kernel

theorem transition0369 : transitionRowCheck seeds row0369 row0370 = true := by
  decide +kernel

theorem transition0370 : transitionRowCheck seeds row0370 row0371 = true := by
  decide +kernel

theorem transition0371 : transitionRowCheck seeds row0371 row0372 = true := by
  decide +kernel

theorem transition0372 : transitionRowCheck seeds row0372 row0373 = true := by
  decide +kernel

theorem transition0373 : transitionRowCheck seeds row0373 row0374 = true := by
  decide +kernel

theorem transition0374 : transitionRowCheck seeds row0374 row0375 = true := by
  decide +kernel

theorem transition0375 : transitionRowCheck seeds row0375 row0376 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
