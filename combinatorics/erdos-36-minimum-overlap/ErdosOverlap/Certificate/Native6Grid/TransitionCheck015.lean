module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows015
public import ErdosOverlap.Certificate.Native6Grid.Rows016

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0120 : transitionRowCheck seeds row0120 row0121 = true := by
  decide +kernel

theorem transition0121 : transitionRowCheck seeds row0121 row0122 = true := by
  decide +kernel

theorem transition0122 : transitionRowCheck seeds row0122 row0123 = true := by
  decide +kernel

theorem transition0123 : transitionRowCheck seeds row0123 row0124 = true := by
  decide +kernel

theorem transition0124 : transitionRowCheck seeds row0124 row0125 = true := by
  decide +kernel

theorem transition0125 : transitionRowCheck seeds row0125 row0126 = true := by
  decide +kernel

theorem transition0126 : transitionRowCheck seeds row0126 row0127 = true := by
  decide +kernel

theorem transition0127 : transitionRowCheck seeds row0127 row0128 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
