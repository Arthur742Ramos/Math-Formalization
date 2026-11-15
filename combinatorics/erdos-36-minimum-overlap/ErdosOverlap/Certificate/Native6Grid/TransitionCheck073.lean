module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows073
public import ErdosOverlap.Certificate.Native6Grid.Rows074

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0584 : transitionRowCheck seeds row0584 row0585 = true := by
  decide +kernel

theorem transition0585 : transitionRowCheck seeds row0585 row0586 = true := by
  decide +kernel

theorem transition0586 : transitionRowCheck seeds row0586 row0587 = true := by
  decide +kernel

theorem transition0587 : transitionRowCheck seeds row0587 row0588 = true := by
  decide +kernel

theorem transition0588 : transitionRowCheck seeds row0588 row0589 = true := by
  decide +kernel

theorem transition0589 : transitionRowCheck seeds row0589 row0590 = true := by
  decide +kernel

theorem transition0590 : transitionRowCheck seeds row0590 row0591 = true := by
  decide +kernel

theorem transition0591 : transitionRowCheck seeds row0591 row0592 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
