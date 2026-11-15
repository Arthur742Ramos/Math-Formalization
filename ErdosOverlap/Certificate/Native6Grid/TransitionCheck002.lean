module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows002
public import ErdosOverlap.Certificate.Native6Grid.Rows003

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0016 : transitionRowCheck seeds row0016 row0017 = true := by
  decide +kernel

theorem transition0017 : transitionRowCheck seeds row0017 row0018 = true := by
  decide +kernel

theorem transition0018 : transitionRowCheck seeds row0018 row0019 = true := by
  decide +kernel

theorem transition0019 : transitionRowCheck seeds row0019 row0020 = true := by
  decide +kernel

theorem transition0020 : transitionRowCheck seeds row0020 row0021 = true := by
  decide +kernel

theorem transition0021 : transitionRowCheck seeds row0021 row0022 = true := by
  decide +kernel

theorem transition0022 : transitionRowCheck seeds row0022 row0023 = true := by
  decide +kernel

theorem transition0023 : transitionRowCheck seeds row0023 row0024 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
