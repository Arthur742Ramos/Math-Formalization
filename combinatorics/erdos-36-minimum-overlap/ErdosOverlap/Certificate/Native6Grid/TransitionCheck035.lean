module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows035
public import ErdosOverlap.Certificate.Native6Grid.Rows036

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0280 : transitionRowCheck seeds row0280 row0281 = true := by
  decide +kernel

theorem transition0281 : transitionRowCheck seeds row0281 row0282 = true := by
  decide +kernel

theorem transition0282 : transitionRowCheck seeds row0282 row0283 = true := by
  decide +kernel

theorem transition0283 : transitionRowCheck seeds row0283 row0284 = true := by
  decide +kernel

theorem transition0284 : transitionRowCheck seeds row0284 row0285 = true := by
  decide +kernel

theorem transition0285 : transitionRowCheck seeds row0285 row0286 = true := by
  decide +kernel

theorem transition0286 : transitionRowCheck seeds row0286 row0287 = true := by
  decide +kernel

theorem transition0287 : transitionRowCheck seeds row0287 row0288 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
