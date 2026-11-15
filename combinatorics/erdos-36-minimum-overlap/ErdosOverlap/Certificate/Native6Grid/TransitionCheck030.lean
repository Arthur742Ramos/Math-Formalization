module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows030
public import ErdosOverlap.Certificate.Native6Grid.Rows031

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0240 : transitionRowCheck seeds row0240 row0241 = true := by
  decide +kernel

theorem transition0241 : transitionRowCheck seeds row0241 row0242 = true := by
  decide +kernel

theorem transition0242 : transitionRowCheck seeds row0242 row0243 = true := by
  decide +kernel

theorem transition0243 : transitionRowCheck seeds row0243 row0244 = true := by
  decide +kernel

theorem transition0244 : transitionRowCheck seeds row0244 row0245 = true := by
  decide +kernel

theorem transition0245 : transitionRowCheck seeds row0245 row0246 = true := by
  decide +kernel

theorem transition0246 : transitionRowCheck seeds row0246 row0247 = true := by
  decide +kernel

theorem transition0247 : transitionRowCheck seeds row0247 row0248 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
