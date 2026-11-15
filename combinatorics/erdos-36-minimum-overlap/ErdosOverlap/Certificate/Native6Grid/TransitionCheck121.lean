module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows121
public import ErdosOverlap.Certificate.Native6Grid.Rows122

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0968 : transitionRowCheck seeds row0968 row0969 = true := by
  decide +kernel

theorem transition0969 : transitionRowCheck seeds row0969 row0970 = true := by
  decide +kernel

theorem transition0970 : transitionRowCheck seeds row0970 row0971 = true := by
  decide +kernel

theorem transition0971 : transitionRowCheck seeds row0971 row0972 = true := by
  decide +kernel

theorem transition0972 : transitionRowCheck seeds row0972 row0973 = true := by
  decide +kernel

theorem transition0973 : transitionRowCheck seeds row0973 row0974 = true := by
  decide +kernel

theorem transition0974 : transitionRowCheck seeds row0974 row0975 = true := by
  decide +kernel

theorem transition0975 : transitionRowCheck seeds row0975 row0976 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
