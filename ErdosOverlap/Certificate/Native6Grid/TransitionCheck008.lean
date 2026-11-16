module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows008
public import ErdosOverlap.Certificate.Native6Grid.Rows009

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0064 : transitionRowCheck seeds row0064 row0065 = true := by
  decide +kernel

theorem transition0065 : transitionRowCheck seeds row0065 row0066 = true := by
  decide +kernel

theorem transition0066 : transitionRowCheck seeds row0066 row0067 = true := by
  decide +kernel

theorem transition0067 : transitionRowCheck seeds row0067 row0068 = true := by
  decide +kernel

theorem transition0068 : transitionRowCheck seeds row0068 row0069 = true := by
  decide +kernel

theorem transition0069 : transitionRowCheck seeds row0069 row0070 = true := by
  decide +kernel

theorem transition0070 : transitionRowCheck seeds row0070 row0071 = true := by
  decide +kernel

theorem transition0071 : transitionRowCheck seeds row0071 row0072 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
