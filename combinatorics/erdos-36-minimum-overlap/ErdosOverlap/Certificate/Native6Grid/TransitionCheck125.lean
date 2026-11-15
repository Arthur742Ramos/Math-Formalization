module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows125
public import ErdosOverlap.Certificate.Native6Grid.Rows126

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition1000 : transitionRowCheck seeds row1000 row1001 = true := by
  decide +kernel

theorem transition1001 : transitionRowCheck seeds row1001 row1002 = true := by
  decide +kernel

theorem transition1002 : transitionRowCheck seeds row1002 row1003 = true := by
  decide +kernel

theorem transition1003 : transitionRowCheck seeds row1003 row1004 = true := by
  decide +kernel

theorem transition1004 : transitionRowCheck seeds row1004 row1005 = true := by
  decide +kernel

theorem transition1005 : transitionRowCheck seeds row1005 row1006 = true := by
  decide +kernel

theorem transition1006 : transitionRowCheck seeds row1006 row1007 = true := by
  decide +kernel

theorem transition1007 : transitionRowCheck seeds row1007 row1008 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
