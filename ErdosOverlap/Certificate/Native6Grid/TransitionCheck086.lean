module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows086
public import ErdosOverlap.Certificate.Native6Grid.Rows087

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0688 : transitionRowCheck seeds row0688 row0689 = true := by
  decide +kernel

theorem transition0689 : transitionRowCheck seeds row0689 row0690 = true := by
  decide +kernel

theorem transition0690 : transitionRowCheck seeds row0690 row0691 = true := by
  decide +kernel

theorem transition0691 : transitionRowCheck seeds row0691 row0692 = true := by
  decide +kernel

theorem transition0692 : transitionRowCheck seeds row0692 row0693 = true := by
  decide +kernel

theorem transition0693 : transitionRowCheck seeds row0693 row0694 = true := by
  decide +kernel

theorem transition0694 : transitionRowCheck seeds row0694 row0695 = true := by
  decide +kernel

theorem transition0695 : transitionRowCheck seeds row0695 row0696 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
