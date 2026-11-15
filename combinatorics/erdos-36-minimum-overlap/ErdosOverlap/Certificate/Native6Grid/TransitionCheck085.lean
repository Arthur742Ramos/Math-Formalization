module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows085
public import ErdosOverlap.Certificate.Native6Grid.Rows086

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0680 : transitionRowCheck seeds row0680 row0681 = true := by
  decide +kernel

theorem transition0681 : transitionRowCheck seeds row0681 row0682 = true := by
  decide +kernel

theorem transition0682 : transitionRowCheck seeds row0682 row0683 = true := by
  decide +kernel

theorem transition0683 : transitionRowCheck seeds row0683 row0684 = true := by
  decide +kernel

theorem transition0684 : transitionRowCheck seeds row0684 row0685 = true := by
  decide +kernel

theorem transition0685 : transitionRowCheck seeds row0685 row0686 = true := by
  decide +kernel

theorem transition0686 : transitionRowCheck seeds row0686 row0687 = true := by
  decide +kernel

theorem transition0687 : transitionRowCheck seeds row0687 row0688 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
