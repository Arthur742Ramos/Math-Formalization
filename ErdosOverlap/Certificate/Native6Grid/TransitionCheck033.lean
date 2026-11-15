module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows033
public import ErdosOverlap.Certificate.Native6Grid.Rows034

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0264 : transitionRowCheck seeds row0264 row0265 = true := by
  decide +kernel

theorem transition0265 : transitionRowCheck seeds row0265 row0266 = true := by
  decide +kernel

theorem transition0266 : transitionRowCheck seeds row0266 row0267 = true := by
  decide +kernel

theorem transition0267 : transitionRowCheck seeds row0267 row0268 = true := by
  decide +kernel

theorem transition0268 : transitionRowCheck seeds row0268 row0269 = true := by
  decide +kernel

theorem transition0269 : transitionRowCheck seeds row0269 row0270 = true := by
  decide +kernel

theorem transition0270 : transitionRowCheck seeds row0270 row0271 = true := by
  decide +kernel

theorem transition0271 : transitionRowCheck seeds row0271 row0272 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
