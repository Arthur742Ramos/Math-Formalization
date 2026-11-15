module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows011
public import ErdosOverlap.Certificate.Native6Grid.Rows012

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0088 : transitionRowCheck seeds row0088 row0089 = true := by
  decide +kernel

theorem transition0089 : transitionRowCheck seeds row0089 row0090 = true := by
  decide +kernel

theorem transition0090 : transitionRowCheck seeds row0090 row0091 = true := by
  decide +kernel

theorem transition0091 : transitionRowCheck seeds row0091 row0092 = true := by
  decide +kernel

theorem transition0092 : transitionRowCheck seeds row0092 row0093 = true := by
  decide +kernel

theorem transition0093 : transitionRowCheck seeds row0093 row0094 = true := by
  decide +kernel

theorem transition0094 : transitionRowCheck seeds row0094 row0095 = true := by
  decide +kernel

theorem transition0095 : transitionRowCheck seeds row0095 row0096 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
