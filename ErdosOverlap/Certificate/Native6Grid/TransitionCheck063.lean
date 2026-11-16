module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows063
public import ErdosOverlap.Certificate.Native6Grid.Rows064

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0504 : transitionRowCheck seeds row0504 row0505 = true := by
  decide +kernel

theorem transition0505 : transitionRowCheck seeds row0505 row0506 = true := by
  decide +kernel

theorem transition0506 : transitionRowCheck seeds row0506 row0507 = true := by
  decide +kernel

theorem transition0507 : transitionRowCheck seeds row0507 row0508 = true := by
  decide +kernel

theorem transition0508 : transitionRowCheck seeds row0508 row0509 = true := by
  decide +kernel

theorem transition0509 : transitionRowCheck seeds row0509 row0510 = true := by
  decide +kernel

theorem transition0510 : transitionRowCheck seeds row0510 row0511 = true := by
  decide +kernel

theorem transition0511 : transitionRowCheck seeds row0511 row0512 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
