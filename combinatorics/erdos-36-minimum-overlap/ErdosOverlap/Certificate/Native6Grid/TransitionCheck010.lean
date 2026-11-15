module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows010
public import ErdosOverlap.Certificate.Native6Grid.Rows011

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0080 : transitionRowCheck seeds row0080 row0081 = true := by
  decide +kernel

theorem transition0081 : transitionRowCheck seeds row0081 row0082 = true := by
  decide +kernel

theorem transition0082 : transitionRowCheck seeds row0082 row0083 = true := by
  decide +kernel

theorem transition0083 : transitionRowCheck seeds row0083 row0084 = true := by
  decide +kernel

theorem transition0084 : transitionRowCheck seeds row0084 row0085 = true := by
  decide +kernel

theorem transition0085 : transitionRowCheck seeds row0085 row0086 = true := by
  decide +kernel

theorem transition0086 : transitionRowCheck seeds row0086 row0087 = true := by
  decide +kernel

theorem transition0087 : transitionRowCheck seeds row0087 row0088 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
