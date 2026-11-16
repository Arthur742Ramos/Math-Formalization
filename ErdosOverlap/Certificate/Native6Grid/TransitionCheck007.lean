module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows007
public import ErdosOverlap.Certificate.Native6Grid.Rows008

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0056 : transitionRowCheck seeds row0056 row0057 = true := by
  decide +kernel

theorem transition0057 : transitionRowCheck seeds row0057 row0058 = true := by
  decide +kernel

theorem transition0058 : transitionRowCheck seeds row0058 row0059 = true := by
  decide +kernel

theorem transition0059 : transitionRowCheck seeds row0059 row0060 = true := by
  decide +kernel

theorem transition0060 : transitionRowCheck seeds row0060 row0061 = true := by
  decide +kernel

theorem transition0061 : transitionRowCheck seeds row0061 row0062 = true := by
  decide +kernel

theorem transition0062 : transitionRowCheck seeds row0062 row0063 = true := by
  decide +kernel

theorem transition0063 : transitionRowCheck seeds row0063 row0064 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
