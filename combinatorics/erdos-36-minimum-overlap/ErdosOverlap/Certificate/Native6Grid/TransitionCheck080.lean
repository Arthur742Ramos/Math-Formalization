module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows080
public import ErdosOverlap.Certificate.Native6Grid.Rows081

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0640 : transitionRowCheck seeds row0640 row0641 = true := by
  decide +kernel

theorem transition0641 : transitionRowCheck seeds row0641 row0642 = true := by
  decide +kernel

theorem transition0642 : transitionRowCheck seeds row0642 row0643 = true := by
  decide +kernel

theorem transition0643 : transitionRowCheck seeds row0643 row0644 = true := by
  decide +kernel

theorem transition0644 : transitionRowCheck seeds row0644 row0645 = true := by
  decide +kernel

theorem transition0645 : transitionRowCheck seeds row0645 row0646 = true := by
  decide +kernel

theorem transition0646 : transitionRowCheck seeds row0646 row0647 = true := by
  decide +kernel

theorem transition0647 : transitionRowCheck seeds row0647 row0648 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
