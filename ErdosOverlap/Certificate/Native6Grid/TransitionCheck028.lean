module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows028
public import ErdosOverlap.Certificate.Native6Grid.Rows029

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0224 : transitionRowCheck seeds row0224 row0225 = true := by
  decide +kernel

theorem transition0225 : transitionRowCheck seeds row0225 row0226 = true := by
  decide +kernel

theorem transition0226 : transitionRowCheck seeds row0226 row0227 = true := by
  decide +kernel

theorem transition0227 : transitionRowCheck seeds row0227 row0228 = true := by
  decide +kernel

theorem transition0228 : transitionRowCheck seeds row0228 row0229 = true := by
  decide +kernel

theorem transition0229 : transitionRowCheck seeds row0229 row0230 = true := by
  decide +kernel

theorem transition0230 : transitionRowCheck seeds row0230 row0231 = true := by
  decide +kernel

theorem transition0231 : transitionRowCheck seeds row0231 row0232 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
