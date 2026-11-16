module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows124
public import ErdosOverlap.Certificate.Native6Grid.Rows125

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0992 : transitionRowCheck seeds row0992 row0993 = true := by
  decide +kernel

theorem transition0993 : transitionRowCheck seeds row0993 row0994 = true := by
  decide +kernel

theorem transition0994 : transitionRowCheck seeds row0994 row0995 = true := by
  decide +kernel

theorem transition0995 : transitionRowCheck seeds row0995 row0996 = true := by
  decide +kernel

theorem transition0996 : transitionRowCheck seeds row0996 row0997 = true := by
  decide +kernel

theorem transition0997 : transitionRowCheck seeds row0997 row0998 = true := by
  decide +kernel

theorem transition0998 : transitionRowCheck seeds row0998 row0999 = true := by
  decide +kernel

theorem transition0999 : transitionRowCheck seeds row0999 row1000 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
