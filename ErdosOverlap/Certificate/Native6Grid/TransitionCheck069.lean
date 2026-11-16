module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows069
public import ErdosOverlap.Certificate.Native6Grid.Rows070

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0552 : transitionRowCheck seeds row0552 row0553 = true := by
  decide +kernel

theorem transition0553 : transitionRowCheck seeds row0553 row0554 = true := by
  decide +kernel

theorem transition0554 : transitionRowCheck seeds row0554 row0555 = true := by
  decide +kernel

theorem transition0555 : transitionRowCheck seeds row0555 row0556 = true := by
  decide +kernel

theorem transition0556 : transitionRowCheck seeds row0556 row0557 = true := by
  decide +kernel

theorem transition0557 : transitionRowCheck seeds row0557 row0558 = true := by
  decide +kernel

theorem transition0558 : transitionRowCheck seeds row0558 row0559 = true := by
  decide +kernel

theorem transition0559 : transitionRowCheck seeds row0559 row0560 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
