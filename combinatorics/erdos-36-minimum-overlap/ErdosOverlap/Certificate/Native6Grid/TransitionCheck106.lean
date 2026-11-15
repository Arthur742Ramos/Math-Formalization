module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows106
public import ErdosOverlap.Certificate.Native6Grid.Rows107

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0848 : transitionRowCheck seeds row0848 row0849 = true := by
  decide +kernel

theorem transition0849 : transitionRowCheck seeds row0849 row0850 = true := by
  decide +kernel

theorem transition0850 : transitionRowCheck seeds row0850 row0851 = true := by
  decide +kernel

theorem transition0851 : transitionRowCheck seeds row0851 row0852 = true := by
  decide +kernel

theorem transition0852 : transitionRowCheck seeds row0852 row0853 = true := by
  decide +kernel

theorem transition0853 : transitionRowCheck seeds row0853 row0854 = true := by
  decide +kernel

theorem transition0854 : transitionRowCheck seeds row0854 row0855 = true := by
  decide +kernel

theorem transition0855 : transitionRowCheck seeds row0855 row0856 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
