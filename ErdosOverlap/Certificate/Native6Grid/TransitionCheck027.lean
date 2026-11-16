module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows027
public import ErdosOverlap.Certificate.Native6Grid.Rows028

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0216 : transitionRowCheck seeds row0216 row0217 = true := by
  decide +kernel

theorem transition0217 : transitionRowCheck seeds row0217 row0218 = true := by
  decide +kernel

theorem transition0218 : transitionRowCheck seeds row0218 row0219 = true := by
  decide +kernel

theorem transition0219 : transitionRowCheck seeds row0219 row0220 = true := by
  decide +kernel

theorem transition0220 : transitionRowCheck seeds row0220 row0221 = true := by
  decide +kernel

theorem transition0221 : transitionRowCheck seeds row0221 row0222 = true := by
  decide +kernel

theorem transition0222 : transitionRowCheck seeds row0222 row0223 = true := by
  decide +kernel

theorem transition0223 : transitionRowCheck seeds row0223 row0224 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
