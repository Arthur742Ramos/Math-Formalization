module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows006
public import ErdosOverlap.Certificate.Native6Grid.Rows007

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0048 : transitionRowCheck seeds row0048 row0049 = true := by
  decide +kernel

theorem transition0049 : transitionRowCheck seeds row0049 row0050 = true := by
  decide +kernel

theorem transition0050 : transitionRowCheck seeds row0050 row0051 = true := by
  decide +kernel

theorem transition0051 : transitionRowCheck seeds row0051 row0052 = true := by
  decide +kernel

theorem transition0052 : transitionRowCheck seeds row0052 row0053 = true := by
  decide +kernel

theorem transition0053 : transitionRowCheck seeds row0053 row0054 = true := by
  decide +kernel

theorem transition0054 : transitionRowCheck seeds row0054 row0055 = true := by
  decide +kernel

theorem transition0055 : transitionRowCheck seeds row0055 row0056 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
