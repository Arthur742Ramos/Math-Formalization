module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows040
public import ErdosOverlap.Certificate.Native6Grid.Rows041

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0320 : transitionRowCheck seeds row0320 row0321 = true := by
  decide +kernel

theorem transition0321 : transitionRowCheck seeds row0321 row0322 = true := by
  decide +kernel

theorem transition0322 : transitionRowCheck seeds row0322 row0323 = true := by
  decide +kernel

theorem transition0323 : transitionRowCheck seeds row0323 row0324 = true := by
  decide +kernel

theorem transition0324 : transitionRowCheck seeds row0324 row0325 = true := by
  decide +kernel

theorem transition0325 : transitionRowCheck seeds row0325 row0326 = true := by
  decide +kernel

theorem transition0326 : transitionRowCheck seeds row0326 row0327 = true := by
  decide +kernel

theorem transition0327 : transitionRowCheck seeds row0327 row0328 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
