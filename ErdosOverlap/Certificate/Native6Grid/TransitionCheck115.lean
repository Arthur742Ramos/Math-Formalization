module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows115
public import ErdosOverlap.Certificate.Native6Grid.Rows116

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0920 : transitionRowCheck seeds row0920 row0921 = true := by
  decide +kernel

theorem transition0921 : transitionRowCheck seeds row0921 row0922 = true := by
  decide +kernel

theorem transition0922 : transitionRowCheck seeds row0922 row0923 = true := by
  decide +kernel

theorem transition0923 : transitionRowCheck seeds row0923 row0924 = true := by
  decide +kernel

theorem transition0924 : transitionRowCheck seeds row0924 row0925 = true := by
  decide +kernel

theorem transition0925 : transitionRowCheck seeds row0925 row0926 = true := by
  decide +kernel

theorem transition0926 : transitionRowCheck seeds row0926 row0927 = true := by
  decide +kernel

theorem transition0927 : transitionRowCheck seeds row0927 row0928 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
