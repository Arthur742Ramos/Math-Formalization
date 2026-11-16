module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows078
public import ErdosOverlap.Certificate.Native6Grid.Rows079

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0624 : transitionRowCheck seeds row0624 row0625 = true := by
  decide +kernel

theorem transition0625 : transitionRowCheck seeds row0625 row0626 = true := by
  decide +kernel

theorem transition0626 : transitionRowCheck seeds row0626 row0627 = true := by
  decide +kernel

theorem transition0627 : transitionRowCheck seeds row0627 row0628 = true := by
  decide +kernel

theorem transition0628 : transitionRowCheck seeds row0628 row0629 = true := by
  decide +kernel

theorem transition0629 : transitionRowCheck seeds row0629 row0630 = true := by
  decide +kernel

theorem transition0630 : transitionRowCheck seeds row0630 row0631 = true := by
  decide +kernel

theorem transition0631 : transitionRowCheck seeds row0631 row0632 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
