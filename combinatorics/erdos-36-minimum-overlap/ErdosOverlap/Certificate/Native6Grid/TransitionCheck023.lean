module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows023
public import ErdosOverlap.Certificate.Native6Grid.Rows024

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0184 : transitionRowCheck seeds row0184 row0185 = true := by
  decide +kernel

theorem transition0185 : transitionRowCheck seeds row0185 row0186 = true := by
  decide +kernel

theorem transition0186 : transitionRowCheck seeds row0186 row0187 = true := by
  decide +kernel

theorem transition0187 : transitionRowCheck seeds row0187 row0188 = true := by
  decide +kernel

theorem transition0188 : transitionRowCheck seeds row0188 row0189 = true := by
  decide +kernel

theorem transition0189 : transitionRowCheck seeds row0189 row0190 = true := by
  decide +kernel

theorem transition0190 : transitionRowCheck seeds row0190 row0191 = true := by
  decide +kernel

theorem transition0191 : transitionRowCheck seeds row0191 row0192 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
