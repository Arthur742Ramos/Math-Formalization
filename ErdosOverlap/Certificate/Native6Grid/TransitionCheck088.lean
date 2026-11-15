module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows088
public import ErdosOverlap.Certificate.Native6Grid.Rows089

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0704 : transitionRowCheck seeds row0704 row0705 = true := by
  decide +kernel

theorem transition0705 : transitionRowCheck seeds row0705 row0706 = true := by
  decide +kernel

theorem transition0706 : transitionRowCheck seeds row0706 row0707 = true := by
  decide +kernel

theorem transition0707 : transitionRowCheck seeds row0707 row0708 = true := by
  decide +kernel

theorem transition0708 : transitionRowCheck seeds row0708 row0709 = true := by
  decide +kernel

theorem transition0709 : transitionRowCheck seeds row0709 row0710 = true := by
  decide +kernel

theorem transition0710 : transitionRowCheck seeds row0710 row0711 = true := by
  decide +kernel

theorem transition0711 : transitionRowCheck seeds row0711 row0712 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
