module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows020
public import ErdosOverlap.Certificate.Native6Grid.Rows021

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0160 : transitionRowCheck seeds row0160 row0161 = true := by
  decide +kernel

theorem transition0161 : transitionRowCheck seeds row0161 row0162 = true := by
  decide +kernel

theorem transition0162 : transitionRowCheck seeds row0162 row0163 = true := by
  decide +kernel

theorem transition0163 : transitionRowCheck seeds row0163 row0164 = true := by
  decide +kernel

theorem transition0164 : transitionRowCheck seeds row0164 row0165 = true := by
  decide +kernel

theorem transition0165 : transitionRowCheck seeds row0165 row0166 = true := by
  decide +kernel

theorem transition0166 : transitionRowCheck seeds row0166 row0167 = true := by
  decide +kernel

theorem transition0167 : transitionRowCheck seeds row0167 row0168 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
