module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows109
public import ErdosOverlap.Certificate.Native6Grid.Rows110

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0872 : transitionRowCheck seeds row0872 row0873 = true := by
  decide +kernel

theorem transition0873 : transitionRowCheck seeds row0873 row0874 = true := by
  decide +kernel

theorem transition0874 : transitionRowCheck seeds row0874 row0875 = true := by
  decide +kernel

theorem transition0875 : transitionRowCheck seeds row0875 row0876 = true := by
  decide +kernel

theorem transition0876 : transitionRowCheck seeds row0876 row0877 = true := by
  decide +kernel

theorem transition0877 : transitionRowCheck seeds row0877 row0878 = true := by
  decide +kernel

theorem transition0878 : transitionRowCheck seeds row0878 row0879 = true := by
  decide +kernel

theorem transition0879 : transitionRowCheck seeds row0879 row0880 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
