module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows025
public import ErdosOverlap.Certificate.Native6Grid.Rows026

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0200 : transitionRowCheck seeds row0200 row0201 = true := by
  decide +kernel

theorem transition0201 : transitionRowCheck seeds row0201 row0202 = true := by
  decide +kernel

theorem transition0202 : transitionRowCheck seeds row0202 row0203 = true := by
  decide +kernel

theorem transition0203 : transitionRowCheck seeds row0203 row0204 = true := by
  decide +kernel

theorem transition0204 : transitionRowCheck seeds row0204 row0205 = true := by
  decide +kernel

theorem transition0205 : transitionRowCheck seeds row0205 row0206 = true := by
  decide +kernel

theorem transition0206 : transitionRowCheck seeds row0206 row0207 = true := by
  decide +kernel

theorem transition0207 : transitionRowCheck seeds row0207 row0208 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
