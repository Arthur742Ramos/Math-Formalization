module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows032
public import ErdosOverlap.Certificate.Native6Grid.Rows033

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0256 : transitionRowCheck seeds row0256 row0257 = true := by
  decide +kernel

theorem transition0257 : transitionRowCheck seeds row0257 row0258 = true := by
  decide +kernel

theorem transition0258 : transitionRowCheck seeds row0258 row0259 = true := by
  decide +kernel

theorem transition0259 : transitionRowCheck seeds row0259 row0260 = true := by
  decide +kernel

theorem transition0260 : transitionRowCheck seeds row0260 row0261 = true := by
  decide +kernel

theorem transition0261 : transitionRowCheck seeds row0261 row0262 = true := by
  decide +kernel

theorem transition0262 : transitionRowCheck seeds row0262 row0263 = true := by
  decide +kernel

theorem transition0263 : transitionRowCheck seeds row0263 row0264 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
