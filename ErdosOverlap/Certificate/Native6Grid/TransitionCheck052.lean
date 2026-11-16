module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows052
public import ErdosOverlap.Certificate.Native6Grid.Rows053

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0416 : transitionRowCheck seeds row0416 row0417 = true := by
  decide +kernel

theorem transition0417 : transitionRowCheck seeds row0417 row0418 = true := by
  decide +kernel

theorem transition0418 : transitionRowCheck seeds row0418 row0419 = true := by
  decide +kernel

theorem transition0419 : transitionRowCheck seeds row0419 row0420 = true := by
  decide +kernel

theorem transition0420 : transitionRowCheck seeds row0420 row0421 = true := by
  decide +kernel

theorem transition0421 : transitionRowCheck seeds row0421 row0422 = true := by
  decide +kernel

theorem transition0422 : transitionRowCheck seeds row0422 row0423 = true := by
  decide +kernel

theorem transition0423 : transitionRowCheck seeds row0423 row0424 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
