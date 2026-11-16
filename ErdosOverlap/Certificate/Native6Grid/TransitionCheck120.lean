module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows120
public import ErdosOverlap.Certificate.Native6Grid.Rows121

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0960 : transitionRowCheck seeds row0960 row0961 = true := by
  decide +kernel

theorem transition0961 : transitionRowCheck seeds row0961 row0962 = true := by
  decide +kernel

theorem transition0962 : transitionRowCheck seeds row0962 row0963 = true := by
  decide +kernel

theorem transition0963 : transitionRowCheck seeds row0963 row0964 = true := by
  decide +kernel

theorem transition0964 : transitionRowCheck seeds row0964 row0965 = true := by
  decide +kernel

theorem transition0965 : transitionRowCheck seeds row0965 row0966 = true := by
  decide +kernel

theorem transition0966 : transitionRowCheck seeds row0966 row0967 = true := by
  decide +kernel

theorem transition0967 : transitionRowCheck seeds row0967 row0968 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
