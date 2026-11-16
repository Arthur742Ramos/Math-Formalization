module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows009
public import ErdosOverlap.Certificate.Native6Grid.Rows010

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0072 : transitionRowCheck seeds row0072 row0073 = true := by
  decide +kernel

theorem transition0073 : transitionRowCheck seeds row0073 row0074 = true := by
  decide +kernel

theorem transition0074 : transitionRowCheck seeds row0074 row0075 = true := by
  decide +kernel

theorem transition0075 : transitionRowCheck seeds row0075 row0076 = true := by
  decide +kernel

theorem transition0076 : transitionRowCheck seeds row0076 row0077 = true := by
  decide +kernel

theorem transition0077 : transitionRowCheck seeds row0077 row0078 = true := by
  decide +kernel

theorem transition0078 : transitionRowCheck seeds row0078 row0079 = true := by
  decide +kernel

theorem transition0079 : transitionRowCheck seeds row0079 row0080 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
