module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows102
public import ErdosOverlap.Certificate.Native6Grid.Rows103

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0816 : transitionRowCheck seeds row0816 row0817 = true := by
  decide +kernel

theorem transition0817 : transitionRowCheck seeds row0817 row0818 = true := by
  decide +kernel

theorem transition0818 : transitionRowCheck seeds row0818 row0819 = true := by
  decide +kernel

theorem transition0819 : transitionRowCheck seeds row0819 row0820 = true := by
  decide +kernel

theorem transition0820 : transitionRowCheck seeds row0820 row0821 = true := by
  decide +kernel

theorem transition0821 : transitionRowCheck seeds row0821 row0822 = true := by
  decide +kernel

theorem transition0822 : transitionRowCheck seeds row0822 row0823 = true := by
  decide +kernel

theorem transition0823 : transitionRowCheck seeds row0823 row0824 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
