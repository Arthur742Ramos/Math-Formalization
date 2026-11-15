module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows110
public import ErdosOverlap.Certificate.Native6Grid.Rows111

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0880 : transitionRowCheck seeds row0880 row0881 = true := by
  decide +kernel

theorem transition0881 : transitionRowCheck seeds row0881 row0882 = true := by
  decide +kernel

theorem transition0882 : transitionRowCheck seeds row0882 row0883 = true := by
  decide +kernel

theorem transition0883 : transitionRowCheck seeds row0883 row0884 = true := by
  decide +kernel

theorem transition0884 : transitionRowCheck seeds row0884 row0885 = true := by
  decide +kernel

theorem transition0885 : transitionRowCheck seeds row0885 row0886 = true := by
  decide +kernel

theorem transition0886 : transitionRowCheck seeds row0886 row0887 = true := by
  decide +kernel

theorem transition0887 : transitionRowCheck seeds row0887 row0888 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
