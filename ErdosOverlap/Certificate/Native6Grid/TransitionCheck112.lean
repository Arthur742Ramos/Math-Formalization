module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows112
public import ErdosOverlap.Certificate.Native6Grid.Rows113

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0896 : transitionRowCheck seeds row0896 row0897 = true := by
  decide +kernel

theorem transition0897 : transitionRowCheck seeds row0897 row0898 = true := by
  decide +kernel

theorem transition0898 : transitionRowCheck seeds row0898 row0899 = true := by
  decide +kernel

theorem transition0899 : transitionRowCheck seeds row0899 row0900 = true := by
  decide +kernel

theorem transition0900 : transitionRowCheck seeds row0900 row0901 = true := by
  decide +kernel

theorem transition0901 : transitionRowCheck seeds row0901 row0902 = true := by
  decide +kernel

theorem transition0902 : transitionRowCheck seeds row0902 row0903 = true := by
  decide +kernel

theorem transition0903 : transitionRowCheck seeds row0903 row0904 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
