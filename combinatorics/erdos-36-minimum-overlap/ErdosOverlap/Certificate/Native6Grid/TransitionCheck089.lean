module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows089
public import ErdosOverlap.Certificate.Native6Grid.Rows090

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0712 : transitionRowCheck seeds row0712 row0713 = true := by
  decide +kernel

theorem transition0713 : transitionRowCheck seeds row0713 row0714 = true := by
  decide +kernel

theorem transition0714 : transitionRowCheck seeds row0714 row0715 = true := by
  decide +kernel

theorem transition0715 : transitionRowCheck seeds row0715 row0716 = true := by
  decide +kernel

theorem transition0716 : transitionRowCheck seeds row0716 row0717 = true := by
  decide +kernel

theorem transition0717 : transitionRowCheck seeds row0717 row0718 = true := by
  decide +kernel

theorem transition0718 : transitionRowCheck seeds row0718 row0719 = true := by
  decide +kernel

theorem transition0719 : transitionRowCheck seeds row0719 row0720 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
