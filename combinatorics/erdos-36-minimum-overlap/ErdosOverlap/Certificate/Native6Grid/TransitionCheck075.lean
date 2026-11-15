module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows075
public import ErdosOverlap.Certificate.Native6Grid.Rows076

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0600 : transitionRowCheck seeds row0600 row0601 = true := by
  decide +kernel

theorem transition0601 : transitionRowCheck seeds row0601 row0602 = true := by
  decide +kernel

theorem transition0602 : transitionRowCheck seeds row0602 row0603 = true := by
  decide +kernel

theorem transition0603 : transitionRowCheck seeds row0603 row0604 = true := by
  decide +kernel

theorem transition0604 : transitionRowCheck seeds row0604 row0605 = true := by
  decide +kernel

theorem transition0605 : transitionRowCheck seeds row0605 row0606 = true := by
  decide +kernel

theorem transition0606 : transitionRowCheck seeds row0606 row0607 = true := by
  decide +kernel

theorem transition0607 : transitionRowCheck seeds row0607 row0608 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
