module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows003
public import ErdosOverlap.Certificate.Native6Grid.Rows004

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0024 : transitionRowCheck seeds row0024 row0025 = true := by
  decide +kernel

theorem transition0025 : transitionRowCheck seeds row0025 row0026 = true := by
  decide +kernel

theorem transition0026 : transitionRowCheck seeds row0026 row0027 = true := by
  decide +kernel

theorem transition0027 : transitionRowCheck seeds row0027 row0028 = true := by
  decide +kernel

theorem transition0028 : transitionRowCheck seeds row0028 row0029 = true := by
  decide +kernel

theorem transition0029 : transitionRowCheck seeds row0029 row0030 = true := by
  decide +kernel

theorem transition0030 : transitionRowCheck seeds row0030 row0031 = true := by
  decide +kernel

theorem transition0031 : transitionRowCheck seeds row0031 row0032 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
