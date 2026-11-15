module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows018
public import ErdosOverlap.Certificate.Native6Grid.Rows019

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0144 : transitionRowCheck seeds row0144 row0145 = true := by
  decide +kernel

theorem transition0145 : transitionRowCheck seeds row0145 row0146 = true := by
  decide +kernel

theorem transition0146 : transitionRowCheck seeds row0146 row0147 = true := by
  decide +kernel

theorem transition0147 : transitionRowCheck seeds row0147 row0148 = true := by
  decide +kernel

theorem transition0148 : transitionRowCheck seeds row0148 row0149 = true := by
  decide +kernel

theorem transition0149 : transitionRowCheck seeds row0149 row0150 = true := by
  decide +kernel

theorem transition0150 : transitionRowCheck seeds row0150 row0151 = true := by
  decide +kernel

theorem transition0151 : transitionRowCheck seeds row0151 row0152 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
