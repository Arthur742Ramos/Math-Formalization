module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows045
public import ErdosOverlap.Certificate.Native6Grid.Rows046

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0360 : transitionRowCheck seeds row0360 row0361 = true := by
  decide +kernel

theorem transition0361 : transitionRowCheck seeds row0361 row0362 = true := by
  decide +kernel

theorem transition0362 : transitionRowCheck seeds row0362 row0363 = true := by
  decide +kernel

theorem transition0363 : transitionRowCheck seeds row0363 row0364 = true := by
  decide +kernel

theorem transition0364 : transitionRowCheck seeds row0364 row0365 = true := by
  decide +kernel

theorem transition0365 : transitionRowCheck seeds row0365 row0366 = true := by
  decide +kernel

theorem transition0366 : transitionRowCheck seeds row0366 row0367 = true := by
  decide +kernel

theorem transition0367 : transitionRowCheck seeds row0367 row0368 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
