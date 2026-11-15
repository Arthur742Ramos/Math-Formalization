module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows096
public import ErdosOverlap.Certificate.Native6Grid.Rows097

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0768 : transitionRowCheck seeds row0768 row0769 = true := by
  decide +kernel

theorem transition0769 : transitionRowCheck seeds row0769 row0770 = true := by
  decide +kernel

theorem transition0770 : transitionRowCheck seeds row0770 row0771 = true := by
  decide +kernel

theorem transition0771 : transitionRowCheck seeds row0771 row0772 = true := by
  decide +kernel

theorem transition0772 : transitionRowCheck seeds row0772 row0773 = true := by
  decide +kernel

theorem transition0773 : transitionRowCheck seeds row0773 row0774 = true := by
  decide +kernel

theorem transition0774 : transitionRowCheck seeds row0774 row0775 = true := by
  decide +kernel

theorem transition0775 : transitionRowCheck seeds row0775 row0776 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
