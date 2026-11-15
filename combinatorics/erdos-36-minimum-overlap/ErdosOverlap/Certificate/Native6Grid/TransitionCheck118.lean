module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows118
public import ErdosOverlap.Certificate.Native6Grid.Rows119

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0944 : transitionRowCheck seeds row0944 row0945 = true := by
  decide +kernel

theorem transition0945 : transitionRowCheck seeds row0945 row0946 = true := by
  decide +kernel

theorem transition0946 : transitionRowCheck seeds row0946 row0947 = true := by
  decide +kernel

theorem transition0947 : transitionRowCheck seeds row0947 row0948 = true := by
  decide +kernel

theorem transition0948 : transitionRowCheck seeds row0948 row0949 = true := by
  decide +kernel

theorem transition0949 : transitionRowCheck seeds row0949 row0950 = true := by
  decide +kernel

theorem transition0950 : transitionRowCheck seeds row0950 row0951 = true := by
  decide +kernel

theorem transition0951 : transitionRowCheck seeds row0951 row0952 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
