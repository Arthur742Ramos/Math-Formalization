module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows016
public import ErdosOverlap.Certificate.Native6Grid.Rows017

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0128 : transitionRowCheck seeds row0128 row0129 = true := by
  decide +kernel

theorem transition0129 : transitionRowCheck seeds row0129 row0130 = true := by
  decide +kernel

theorem transition0130 : transitionRowCheck seeds row0130 row0131 = true := by
  decide +kernel

theorem transition0131 : transitionRowCheck seeds row0131 row0132 = true := by
  decide +kernel

theorem transition0132 : transitionRowCheck seeds row0132 row0133 = true := by
  decide +kernel

theorem transition0133 : transitionRowCheck seeds row0133 row0134 = true := by
  decide +kernel

theorem transition0134 : transitionRowCheck seeds row0134 row0135 = true := by
  decide +kernel

theorem transition0135 : transitionRowCheck seeds row0135 row0136 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
