module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows070
public import ErdosOverlap.Certificate.Native6Grid.Rows071

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0560 : transitionRowCheck seeds row0560 row0561 = true := by
  decide +kernel

theorem transition0561 : transitionRowCheck seeds row0561 row0562 = true := by
  decide +kernel

theorem transition0562 : transitionRowCheck seeds row0562 row0563 = true := by
  decide +kernel

theorem transition0563 : transitionRowCheck seeds row0563 row0564 = true := by
  decide +kernel

theorem transition0564 : transitionRowCheck seeds row0564 row0565 = true := by
  decide +kernel

theorem transition0565 : transitionRowCheck seeds row0565 row0566 = true := by
  decide +kernel

theorem transition0566 : transitionRowCheck seeds row0566 row0567 = true := by
  decide +kernel

theorem transition0567 : transitionRowCheck seeds row0567 row0568 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
