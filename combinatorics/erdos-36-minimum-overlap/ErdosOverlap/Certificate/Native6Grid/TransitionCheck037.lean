module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows037
public import ErdosOverlap.Certificate.Native6Grid.Rows038

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0296 : transitionRowCheck seeds row0296 row0297 = true := by
  decide +kernel

theorem transition0297 : transitionRowCheck seeds row0297 row0298 = true := by
  decide +kernel

theorem transition0298 : transitionRowCheck seeds row0298 row0299 = true := by
  decide +kernel

theorem transition0299 : transitionRowCheck seeds row0299 row0300 = true := by
  decide +kernel

theorem transition0300 : transitionRowCheck seeds row0300 row0301 = true := by
  decide +kernel

theorem transition0301 : transitionRowCheck seeds row0301 row0302 = true := by
  decide +kernel

theorem transition0302 : transitionRowCheck seeds row0302 row0303 = true := by
  decide +kernel

theorem transition0303 : transitionRowCheck seeds row0303 row0304 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
