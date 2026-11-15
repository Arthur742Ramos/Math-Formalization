module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows029
public import ErdosOverlap.Certificate.Native6Grid.Rows030

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0232 : transitionRowCheck seeds row0232 row0233 = true := by
  decide +kernel

theorem transition0233 : transitionRowCheck seeds row0233 row0234 = true := by
  decide +kernel

theorem transition0234 : transitionRowCheck seeds row0234 row0235 = true := by
  decide +kernel

theorem transition0235 : transitionRowCheck seeds row0235 row0236 = true := by
  decide +kernel

theorem transition0236 : transitionRowCheck seeds row0236 row0237 = true := by
  decide +kernel

theorem transition0237 : transitionRowCheck seeds row0237 row0238 = true := by
  decide +kernel

theorem transition0238 : transitionRowCheck seeds row0238 row0239 = true := by
  decide +kernel

theorem transition0239 : transitionRowCheck seeds row0239 row0240 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
