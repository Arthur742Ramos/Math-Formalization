module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows101
public import ErdosOverlap.Certificate.Native6Grid.Rows102

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0808 : transitionRowCheck seeds row0808 row0809 = true := by
  decide +kernel

theorem transition0809 : transitionRowCheck seeds row0809 row0810 = true := by
  decide +kernel

theorem transition0810 : transitionRowCheck seeds row0810 row0811 = true := by
  decide +kernel

theorem transition0811 : transitionRowCheck seeds row0811 row0812 = true := by
  decide +kernel

theorem transition0812 : transitionRowCheck seeds row0812 row0813 = true := by
  decide +kernel

theorem transition0813 : transitionRowCheck seeds row0813 row0814 = true := by
  decide +kernel

theorem transition0814 : transitionRowCheck seeds row0814 row0815 = true := by
  decide +kernel

theorem transition0815 : transitionRowCheck seeds row0815 row0816 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
