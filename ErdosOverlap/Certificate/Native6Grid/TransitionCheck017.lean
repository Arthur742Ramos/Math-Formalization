module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows017
public import ErdosOverlap.Certificate.Native6Grid.Rows018

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0136 : transitionRowCheck seeds row0136 row0137 = true := by
  decide +kernel

theorem transition0137 : transitionRowCheck seeds row0137 row0138 = true := by
  decide +kernel

theorem transition0138 : transitionRowCheck seeds row0138 row0139 = true := by
  decide +kernel

theorem transition0139 : transitionRowCheck seeds row0139 row0140 = true := by
  decide +kernel

theorem transition0140 : transitionRowCheck seeds row0140 row0141 = true := by
  decide +kernel

theorem transition0141 : transitionRowCheck seeds row0141 row0142 = true := by
  decide +kernel

theorem transition0142 : transitionRowCheck seeds row0142 row0143 = true := by
  decide +kernel

theorem transition0143 : transitionRowCheck seeds row0143 row0144 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
