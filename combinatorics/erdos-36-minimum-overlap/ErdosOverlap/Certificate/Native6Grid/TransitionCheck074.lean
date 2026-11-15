module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows074
public import ErdosOverlap.Certificate.Native6Grid.Rows075

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0592 : transitionRowCheck seeds row0592 row0593 = true := by
  decide +kernel

theorem transition0593 : transitionRowCheck seeds row0593 row0594 = true := by
  decide +kernel

theorem transition0594 : transitionRowCheck seeds row0594 row0595 = true := by
  decide +kernel

theorem transition0595 : transitionRowCheck seeds row0595 row0596 = true := by
  decide +kernel

theorem transition0596 : transitionRowCheck seeds row0596 row0597 = true := by
  decide +kernel

theorem transition0597 : transitionRowCheck seeds row0597 row0598 = true := by
  decide +kernel

theorem transition0598 : transitionRowCheck seeds row0598 row0599 = true := by
  decide +kernel

theorem transition0599 : transitionRowCheck seeds row0599 row0600 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
