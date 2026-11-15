module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows100
public import ErdosOverlap.Certificate.Native6Grid.Rows101

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0800 : transitionRowCheck seeds row0800 row0801 = true := by
  decide +kernel

theorem transition0801 : transitionRowCheck seeds row0801 row0802 = true := by
  decide +kernel

theorem transition0802 : transitionRowCheck seeds row0802 row0803 = true := by
  decide +kernel

theorem transition0803 : transitionRowCheck seeds row0803 row0804 = true := by
  decide +kernel

theorem transition0804 : transitionRowCheck seeds row0804 row0805 = true := by
  decide +kernel

theorem transition0805 : transitionRowCheck seeds row0805 row0806 = true := by
  decide +kernel

theorem transition0806 : transitionRowCheck seeds row0806 row0807 = true := by
  decide +kernel

theorem transition0807 : transitionRowCheck seeds row0807 row0808 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
