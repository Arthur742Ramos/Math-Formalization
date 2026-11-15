module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows000
public import ErdosOverlap.Certificate.Native6Grid.Rows001

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0000 : transitionRowCheck seeds row0000 row0001 = true := by
  decide +kernel

theorem transition0001 : transitionRowCheck seeds row0001 row0002 = true := by
  decide +kernel

theorem transition0002 : transitionRowCheck seeds row0002 row0003 = true := by
  decide +kernel

theorem transition0003 : transitionRowCheck seeds row0003 row0004 = true := by
  decide +kernel

theorem transition0004 : transitionRowCheck seeds row0004 row0005 = true := by
  decide +kernel

theorem transition0005 : transitionRowCheck seeds row0005 row0006 = true := by
  decide +kernel

theorem transition0006 : transitionRowCheck seeds row0006 row0007 = true := by
  decide +kernel

theorem transition0007 : transitionRowCheck seeds row0007 row0008 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
