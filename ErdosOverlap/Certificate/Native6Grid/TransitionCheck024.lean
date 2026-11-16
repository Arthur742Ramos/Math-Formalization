module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows024
public import ErdosOverlap.Certificate.Native6Grid.Rows025

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0192 : transitionRowCheck seeds row0192 row0193 = true := by
  decide +kernel

theorem transition0193 : transitionRowCheck seeds row0193 row0194 = true := by
  decide +kernel

theorem transition0194 : transitionRowCheck seeds row0194 row0195 = true := by
  decide +kernel

theorem transition0195 : transitionRowCheck seeds row0195 row0196 = true := by
  decide +kernel

theorem transition0196 : transitionRowCheck seeds row0196 row0197 = true := by
  decide +kernel

theorem transition0197 : transitionRowCheck seeds row0197 row0198 = true := by
  decide +kernel

theorem transition0198 : transitionRowCheck seeds row0198 row0199 = true := by
  decide +kernel

theorem transition0199 : transitionRowCheck seeds row0199 row0200 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
