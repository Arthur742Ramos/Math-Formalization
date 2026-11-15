module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows097
public import ErdosOverlap.Certificate.Native6Grid.Rows098

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0776 : transitionRowCheck seeds row0776 row0777 = true := by
  decide +kernel

theorem transition0777 : transitionRowCheck seeds row0777 row0778 = true := by
  decide +kernel

theorem transition0778 : transitionRowCheck seeds row0778 row0779 = true := by
  decide +kernel

theorem transition0779 : transitionRowCheck seeds row0779 row0780 = true := by
  decide +kernel

theorem transition0780 : transitionRowCheck seeds row0780 row0781 = true := by
  decide +kernel

theorem transition0781 : transitionRowCheck seeds row0781 row0782 = true := by
  decide +kernel

theorem transition0782 : transitionRowCheck seeds row0782 row0783 = true := by
  decide +kernel

theorem transition0783 : transitionRowCheck seeds row0783 row0784 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
