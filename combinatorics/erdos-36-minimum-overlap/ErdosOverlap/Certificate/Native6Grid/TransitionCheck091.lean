module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows091
public import ErdosOverlap.Certificate.Native6Grid.Rows092

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0728 : transitionRowCheck seeds row0728 row0729 = true := by
  decide +kernel

theorem transition0729 : transitionRowCheck seeds row0729 row0730 = true := by
  decide +kernel

theorem transition0730 : transitionRowCheck seeds row0730 row0731 = true := by
  decide +kernel

theorem transition0731 : transitionRowCheck seeds row0731 row0732 = true := by
  decide +kernel

theorem transition0732 : transitionRowCheck seeds row0732 row0733 = true := by
  decide +kernel

theorem transition0733 : transitionRowCheck seeds row0733 row0734 = true := by
  decide +kernel

theorem transition0734 : transitionRowCheck seeds row0734 row0735 = true := by
  decide +kernel

theorem transition0735 : transitionRowCheck seeds row0735 row0736 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
