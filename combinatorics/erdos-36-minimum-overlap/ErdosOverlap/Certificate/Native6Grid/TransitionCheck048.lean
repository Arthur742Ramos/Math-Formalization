module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows048
public import ErdosOverlap.Certificate.Native6Grid.Rows049

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0384 : transitionRowCheck seeds row0384 row0385 = true := by
  decide +kernel

theorem transition0385 : transitionRowCheck seeds row0385 row0386 = true := by
  decide +kernel

theorem transition0386 : transitionRowCheck seeds row0386 row0387 = true := by
  decide +kernel

theorem transition0387 : transitionRowCheck seeds row0387 row0388 = true := by
  decide +kernel

theorem transition0388 : transitionRowCheck seeds row0388 row0389 = true := by
  decide +kernel

theorem transition0389 : transitionRowCheck seeds row0389 row0390 = true := by
  decide +kernel

theorem transition0390 : transitionRowCheck seeds row0390 row0391 = true := by
  decide +kernel

theorem transition0391 : transitionRowCheck seeds row0391 row0392 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
