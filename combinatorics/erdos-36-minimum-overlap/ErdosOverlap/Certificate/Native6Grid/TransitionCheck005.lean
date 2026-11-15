module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows005
public import ErdosOverlap.Certificate.Native6Grid.Rows006

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0040 : transitionRowCheck seeds row0040 row0041 = true := by
  decide +kernel

theorem transition0041 : transitionRowCheck seeds row0041 row0042 = true := by
  decide +kernel

theorem transition0042 : transitionRowCheck seeds row0042 row0043 = true := by
  decide +kernel

theorem transition0043 : transitionRowCheck seeds row0043 row0044 = true := by
  decide +kernel

theorem transition0044 : transitionRowCheck seeds row0044 row0045 = true := by
  decide +kernel

theorem transition0045 : transitionRowCheck seeds row0045 row0046 = true := by
  decide +kernel

theorem transition0046 : transitionRowCheck seeds row0046 row0047 = true := by
  decide +kernel

theorem transition0047 : transitionRowCheck seeds row0047 row0048 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
