module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows039
public import ErdosOverlap.Certificate.Native6Grid.Rows040

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0312 : transitionRowCheck seeds row0312 row0313 = true := by
  decide +kernel

theorem transition0313 : transitionRowCheck seeds row0313 row0314 = true := by
  decide +kernel

theorem transition0314 : transitionRowCheck seeds row0314 row0315 = true := by
  decide +kernel

theorem transition0315 : transitionRowCheck seeds row0315 row0316 = true := by
  decide +kernel

theorem transition0316 : transitionRowCheck seeds row0316 row0317 = true := by
  decide +kernel

theorem transition0317 : transitionRowCheck seeds row0317 row0318 = true := by
  decide +kernel

theorem transition0318 : transitionRowCheck seeds row0318 row0319 = true := by
  decide +kernel

theorem transition0319 : transitionRowCheck seeds row0319 row0320 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
