module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows127

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition1016 : transitionRowCheck seeds row1016 row1017 = true := by
  decide +kernel

theorem transition1017 : transitionRowCheck seeds row1017 row1018 = true := by
  decide +kernel

theorem transition1018 : transitionRowCheck seeds row1018 row1019 = true := by
  decide +kernel

theorem transition1019 : transitionRowCheck seeds row1019 row1020 = true := by
  decide +kernel

theorem transition1020 : transitionRowCheck seeds row1020 row1021 = true := by
  decide +kernel

theorem transition1021 : transitionRowCheck seeds row1021 row1022 = true := by
  decide +kernel

theorem transition1022 : transitionRowCheck seeds row1022 row1023 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
