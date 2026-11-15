module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows021
public import ErdosOverlap.Certificate.Native6Grid.Rows022

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0168 : transitionRowCheck seeds row0168 row0169 = true := by
  decide +kernel

theorem transition0169 : transitionRowCheck seeds row0169 row0170 = true := by
  decide +kernel

theorem transition0170 : transitionRowCheck seeds row0170 row0171 = true := by
  decide +kernel

theorem transition0171 : transitionRowCheck seeds row0171 row0172 = true := by
  decide +kernel

theorem transition0172 : transitionRowCheck seeds row0172 row0173 = true := by
  decide +kernel

theorem transition0173 : transitionRowCheck seeds row0173 row0174 = true := by
  decide +kernel

theorem transition0174 : transitionRowCheck seeds row0174 row0175 = true := by
  decide +kernel

theorem transition0175 : transitionRowCheck seeds row0175 row0176 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
