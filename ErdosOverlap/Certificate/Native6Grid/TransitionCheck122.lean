module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows122
public import ErdosOverlap.Certificate.Native6Grid.Rows123

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0976 : transitionRowCheck seeds row0976 row0977 = true := by
  decide +kernel

theorem transition0977 : transitionRowCheck seeds row0977 row0978 = true := by
  decide +kernel

theorem transition0978 : transitionRowCheck seeds row0978 row0979 = true := by
  decide +kernel

theorem transition0979 : transitionRowCheck seeds row0979 row0980 = true := by
  decide +kernel

theorem transition0980 : transitionRowCheck seeds row0980 row0981 = true := by
  decide +kernel

theorem transition0981 : transitionRowCheck seeds row0981 row0982 = true := by
  decide +kernel

theorem transition0982 : transitionRowCheck seeds row0982 row0983 = true := by
  decide +kernel

theorem transition0983 : transitionRowCheck seeds row0983 row0984 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
