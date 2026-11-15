module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows099
public import ErdosOverlap.Certificate.Native6Grid.Rows100

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0792 : transitionRowCheck seeds row0792 row0793 = true := by
  decide +kernel

theorem transition0793 : transitionRowCheck seeds row0793 row0794 = true := by
  decide +kernel

theorem transition0794 : transitionRowCheck seeds row0794 row0795 = true := by
  decide +kernel

theorem transition0795 : transitionRowCheck seeds row0795 row0796 = true := by
  decide +kernel

theorem transition0796 : transitionRowCheck seeds row0796 row0797 = true := by
  decide +kernel

theorem transition0797 : transitionRowCheck seeds row0797 row0798 = true := by
  decide +kernel

theorem transition0798 : transitionRowCheck seeds row0798 row0799 = true := by
  decide +kernel

theorem transition0799 : transitionRowCheck seeds row0799 row0800 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
