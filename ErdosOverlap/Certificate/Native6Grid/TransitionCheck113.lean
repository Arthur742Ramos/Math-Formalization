module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows113
public import ErdosOverlap.Certificate.Native6Grid.Rows114

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0904 : transitionRowCheck seeds row0904 row0905 = true := by
  decide +kernel

theorem transition0905 : transitionRowCheck seeds row0905 row0906 = true := by
  decide +kernel

theorem transition0906 : transitionRowCheck seeds row0906 row0907 = true := by
  decide +kernel

theorem transition0907 : transitionRowCheck seeds row0907 row0908 = true := by
  decide +kernel

theorem transition0908 : transitionRowCheck seeds row0908 row0909 = true := by
  decide +kernel

theorem transition0909 : transitionRowCheck seeds row0909 row0910 = true := by
  decide +kernel

theorem transition0910 : transitionRowCheck seeds row0910 row0911 = true := by
  decide +kernel

theorem transition0911 : transitionRowCheck seeds row0911 row0912 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
