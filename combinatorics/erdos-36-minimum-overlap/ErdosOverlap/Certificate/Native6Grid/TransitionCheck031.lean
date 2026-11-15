module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows031
public import ErdosOverlap.Certificate.Native6Grid.Rows032

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0248 : transitionRowCheck seeds row0248 row0249 = true := by
  decide +kernel

theorem transition0249 : transitionRowCheck seeds row0249 row0250 = true := by
  decide +kernel

theorem transition0250 : transitionRowCheck seeds row0250 row0251 = true := by
  decide +kernel

theorem transition0251 : transitionRowCheck seeds row0251 row0252 = true := by
  decide +kernel

theorem transition0252 : transitionRowCheck seeds row0252 row0253 = true := by
  decide +kernel

theorem transition0253 : transitionRowCheck seeds row0253 row0254 = true := by
  decide +kernel

theorem transition0254 : transitionRowCheck seeds row0254 row0255 = true := by
  decide +kernel

theorem transition0255 : transitionRowCheck seeds row0255 row0256 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
