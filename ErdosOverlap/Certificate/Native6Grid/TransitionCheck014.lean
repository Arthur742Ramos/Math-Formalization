module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows014
public import ErdosOverlap.Certificate.Native6Grid.Rows015

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0112 : transitionRowCheck seeds row0112 row0113 = true := by
  decide +kernel

theorem transition0113 : transitionRowCheck seeds row0113 row0114 = true := by
  decide +kernel

theorem transition0114 : transitionRowCheck seeds row0114 row0115 = true := by
  decide +kernel

theorem transition0115 : transitionRowCheck seeds row0115 row0116 = true := by
  decide +kernel

theorem transition0116 : transitionRowCheck seeds row0116 row0117 = true := by
  decide +kernel

theorem transition0117 : transitionRowCheck seeds row0117 row0118 = true := by
  decide +kernel

theorem transition0118 : transitionRowCheck seeds row0118 row0119 = true := by
  decide +kernel

theorem transition0119 : transitionRowCheck seeds row0119 row0120 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
