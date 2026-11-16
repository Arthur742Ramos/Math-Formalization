module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows111
public import ErdosOverlap.Certificate.Native6Grid.Rows112

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0888 : transitionRowCheck seeds row0888 row0889 = true := by
  decide +kernel

theorem transition0889 : transitionRowCheck seeds row0889 row0890 = true := by
  decide +kernel

theorem transition0890 : transitionRowCheck seeds row0890 row0891 = true := by
  decide +kernel

theorem transition0891 : transitionRowCheck seeds row0891 row0892 = true := by
  decide +kernel

theorem transition0892 : transitionRowCheck seeds row0892 row0893 = true := by
  decide +kernel

theorem transition0893 : transitionRowCheck seeds row0893 row0894 = true := by
  decide +kernel

theorem transition0894 : transitionRowCheck seeds row0894 row0895 = true := by
  decide +kernel

theorem transition0895 : transitionRowCheck seeds row0895 row0896 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
