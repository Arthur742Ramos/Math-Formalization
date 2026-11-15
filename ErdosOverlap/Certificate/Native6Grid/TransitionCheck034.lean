module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows034
public import ErdosOverlap.Certificate.Native6Grid.Rows035

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0272 : transitionRowCheck seeds row0272 row0273 = true := by
  decide +kernel

theorem transition0273 : transitionRowCheck seeds row0273 row0274 = true := by
  decide +kernel

theorem transition0274 : transitionRowCheck seeds row0274 row0275 = true := by
  decide +kernel

theorem transition0275 : transitionRowCheck seeds row0275 row0276 = true := by
  decide +kernel

theorem transition0276 : transitionRowCheck seeds row0276 row0277 = true := by
  decide +kernel

theorem transition0277 : transitionRowCheck seeds row0277 row0278 = true := by
  decide +kernel

theorem transition0278 : transitionRowCheck seeds row0278 row0279 = true := by
  decide +kernel

theorem transition0279 : transitionRowCheck seeds row0279 row0280 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
