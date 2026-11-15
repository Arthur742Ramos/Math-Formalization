module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows001
public import ErdosOverlap.Certificate.Native6Grid.Rows002

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0008 : transitionRowCheck seeds row0008 row0009 = true := by
  decide +kernel

theorem transition0009 : transitionRowCheck seeds row0009 row0010 = true := by
  decide +kernel

theorem transition0010 : transitionRowCheck seeds row0010 row0011 = true := by
  decide +kernel

theorem transition0011 : transitionRowCheck seeds row0011 row0012 = true := by
  decide +kernel

theorem transition0012 : transitionRowCheck seeds row0012 row0013 = true := by
  decide +kernel

theorem transition0013 : transitionRowCheck seeds row0013 row0014 = true := by
  decide +kernel

theorem transition0014 : transitionRowCheck seeds row0014 row0015 = true := by
  decide +kernel

theorem transition0015 : transitionRowCheck seeds row0015 row0016 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
