module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows044
public import ErdosOverlap.Certificate.Native6Grid.Rows045

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0352 : transitionRowCheck seeds row0352 row0353 = true := by
  decide +kernel

theorem transition0353 : transitionRowCheck seeds row0353 row0354 = true := by
  decide +kernel

theorem transition0354 : transitionRowCheck seeds row0354 row0355 = true := by
  decide +kernel

theorem transition0355 : transitionRowCheck seeds row0355 row0356 = true := by
  decide +kernel

theorem transition0356 : transitionRowCheck seeds row0356 row0357 = true := by
  decide +kernel

theorem transition0357 : transitionRowCheck seeds row0357 row0358 = true := by
  decide +kernel

theorem transition0358 : transitionRowCheck seeds row0358 row0359 = true := by
  decide +kernel

theorem transition0359 : transitionRowCheck seeds row0359 row0360 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
