module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows064
public import ErdosOverlap.Certificate.Native6Grid.Rows065

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0512 : transitionRowCheck seeds row0512 row0513 = true := by
  decide +kernel

theorem transition0513 : transitionRowCheck seeds row0513 row0514 = true := by
  decide +kernel

theorem transition0514 : transitionRowCheck seeds row0514 row0515 = true := by
  decide +kernel

theorem transition0515 : transitionRowCheck seeds row0515 row0516 = true := by
  decide +kernel

theorem transition0516 : transitionRowCheck seeds row0516 row0517 = true := by
  decide +kernel

theorem transition0517 : transitionRowCheck seeds row0517 row0518 = true := by
  decide +kernel

theorem transition0518 : transitionRowCheck seeds row0518 row0519 = true := by
  decide +kernel

theorem transition0519 : transitionRowCheck seeds row0519 row0520 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
