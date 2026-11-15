module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows098
public import ErdosOverlap.Certificate.Native6Grid.Rows099

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0784 : transitionRowCheck seeds row0784 row0785 = true := by
  decide +kernel

theorem transition0785 : transitionRowCheck seeds row0785 row0786 = true := by
  decide +kernel

theorem transition0786 : transitionRowCheck seeds row0786 row0787 = true := by
  decide +kernel

theorem transition0787 : transitionRowCheck seeds row0787 row0788 = true := by
  decide +kernel

theorem transition0788 : transitionRowCheck seeds row0788 row0789 = true := by
  decide +kernel

theorem transition0789 : transitionRowCheck seeds row0789 row0790 = true := by
  decide +kernel

theorem transition0790 : transitionRowCheck seeds row0790 row0791 = true := by
  decide +kernel

theorem transition0791 : transitionRowCheck seeds row0791 row0792 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
