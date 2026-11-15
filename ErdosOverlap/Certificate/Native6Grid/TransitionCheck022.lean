module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows022
public import ErdosOverlap.Certificate.Native6Grid.Rows023

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0176 : transitionRowCheck seeds row0176 row0177 = true := by
  decide +kernel

theorem transition0177 : transitionRowCheck seeds row0177 row0178 = true := by
  decide +kernel

theorem transition0178 : transitionRowCheck seeds row0178 row0179 = true := by
  decide +kernel

theorem transition0179 : transitionRowCheck seeds row0179 row0180 = true := by
  decide +kernel

theorem transition0180 : transitionRowCheck seeds row0180 row0181 = true := by
  decide +kernel

theorem transition0181 : transitionRowCheck seeds row0181 row0182 = true := by
  decide +kernel

theorem transition0182 : transitionRowCheck seeds row0182 row0183 = true := by
  decide +kernel

theorem transition0183 : transitionRowCheck seeds row0183 row0184 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
