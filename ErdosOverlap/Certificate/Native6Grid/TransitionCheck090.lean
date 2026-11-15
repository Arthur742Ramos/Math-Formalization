module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows090
public import ErdosOverlap.Certificate.Native6Grid.Rows091

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0720 : transitionRowCheck seeds row0720 row0721 = true := by
  decide +kernel

theorem transition0721 : transitionRowCheck seeds row0721 row0722 = true := by
  decide +kernel

theorem transition0722 : transitionRowCheck seeds row0722 row0723 = true := by
  decide +kernel

theorem transition0723 : transitionRowCheck seeds row0723 row0724 = true := by
  decide +kernel

theorem transition0724 : transitionRowCheck seeds row0724 row0725 = true := by
  decide +kernel

theorem transition0725 : transitionRowCheck seeds row0725 row0726 = true := by
  decide +kernel

theorem transition0726 : transitionRowCheck seeds row0726 row0727 = true := by
  decide +kernel

theorem transition0727 : transitionRowCheck seeds row0727 row0728 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
