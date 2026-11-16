module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows077
public import ErdosOverlap.Certificate.Native6Grid.Rows078

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0616 : transitionRowCheck seeds row0616 row0617 = true := by
  decide +kernel

theorem transition0617 : transitionRowCheck seeds row0617 row0618 = true := by
  decide +kernel

theorem transition0618 : transitionRowCheck seeds row0618 row0619 = true := by
  decide +kernel

theorem transition0619 : transitionRowCheck seeds row0619 row0620 = true := by
  decide +kernel

theorem transition0620 : transitionRowCheck seeds row0620 row0621 = true := by
  decide +kernel

theorem transition0621 : transitionRowCheck seeds row0621 row0622 = true := by
  decide +kernel

theorem transition0622 : transitionRowCheck seeds row0622 row0623 = true := by
  decide +kernel

theorem transition0623 : transitionRowCheck seeds row0623 row0624 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
