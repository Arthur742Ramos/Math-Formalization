module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows083
public import ErdosOverlap.Certificate.Native6Grid.Rows084

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0664 : transitionRowCheck seeds row0664 row0665 = true := by
  decide +kernel

theorem transition0665 : transitionRowCheck seeds row0665 row0666 = true := by
  decide +kernel

theorem transition0666 : transitionRowCheck seeds row0666 row0667 = true := by
  decide +kernel

theorem transition0667 : transitionRowCheck seeds row0667 row0668 = true := by
  decide +kernel

theorem transition0668 : transitionRowCheck seeds row0668 row0669 = true := by
  decide +kernel

theorem transition0669 : transitionRowCheck seeds row0669 row0670 = true := by
  decide +kernel

theorem transition0670 : transitionRowCheck seeds row0670 row0671 = true := by
  decide +kernel

theorem transition0671 : transitionRowCheck seeds row0671 row0672 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
