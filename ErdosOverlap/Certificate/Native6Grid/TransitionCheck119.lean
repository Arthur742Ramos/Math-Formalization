module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows119
public import ErdosOverlap.Certificate.Native6Grid.Rows120

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0952 : transitionRowCheck seeds row0952 row0953 = true := by
  decide +kernel

theorem transition0953 : transitionRowCheck seeds row0953 row0954 = true := by
  decide +kernel

theorem transition0954 : transitionRowCheck seeds row0954 row0955 = true := by
  decide +kernel

theorem transition0955 : transitionRowCheck seeds row0955 row0956 = true := by
  decide +kernel

theorem transition0956 : transitionRowCheck seeds row0956 row0957 = true := by
  decide +kernel

theorem transition0957 : transitionRowCheck seeds row0957 row0958 = true := by
  decide +kernel

theorem transition0958 : transitionRowCheck seeds row0958 row0959 = true := by
  decide +kernel

theorem transition0959 : transitionRowCheck seeds row0959 row0960 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
