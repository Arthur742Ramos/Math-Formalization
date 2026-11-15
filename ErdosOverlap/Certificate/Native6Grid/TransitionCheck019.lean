module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows019
public import ErdosOverlap.Certificate.Native6Grid.Rows020

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0152 : transitionRowCheck seeds row0152 row0153 = true := by
  decide +kernel

theorem transition0153 : transitionRowCheck seeds row0153 row0154 = true := by
  decide +kernel

theorem transition0154 : transitionRowCheck seeds row0154 row0155 = true := by
  decide +kernel

theorem transition0155 : transitionRowCheck seeds row0155 row0156 = true := by
  decide +kernel

theorem transition0156 : transitionRowCheck seeds row0156 row0157 = true := by
  decide +kernel

theorem transition0157 : transitionRowCheck seeds row0157 row0158 = true := by
  decide +kernel

theorem transition0158 : transitionRowCheck seeds row0158 row0159 = true := by
  decide +kernel

theorem transition0159 : transitionRowCheck seeds row0159 row0160 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
