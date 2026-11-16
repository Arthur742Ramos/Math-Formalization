module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows004
public import ErdosOverlap.Certificate.Native6Grid.Rows005

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0032 : transitionRowCheck seeds row0032 row0033 = true := by
  decide +kernel

theorem transition0033 : transitionRowCheck seeds row0033 row0034 = true := by
  decide +kernel

theorem transition0034 : transitionRowCheck seeds row0034 row0035 = true := by
  decide +kernel

theorem transition0035 : transitionRowCheck seeds row0035 row0036 = true := by
  decide +kernel

theorem transition0036 : transitionRowCheck seeds row0036 row0037 = true := by
  decide +kernel

theorem transition0037 : transitionRowCheck seeds row0037 row0038 = true := by
  decide +kernel

theorem transition0038 : transitionRowCheck seeds row0038 row0039 = true := by
  decide +kernel

theorem transition0039 : transitionRowCheck seeds row0039 row0040 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
