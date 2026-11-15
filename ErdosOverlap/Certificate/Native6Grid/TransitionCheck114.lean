module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows114
public import ErdosOverlap.Certificate.Native6Grid.Rows115

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0912 : transitionRowCheck seeds row0912 row0913 = true := by
  decide +kernel

theorem transition0913 : transitionRowCheck seeds row0913 row0914 = true := by
  decide +kernel

theorem transition0914 : transitionRowCheck seeds row0914 row0915 = true := by
  decide +kernel

theorem transition0915 : transitionRowCheck seeds row0915 row0916 = true := by
  decide +kernel

theorem transition0916 : transitionRowCheck seeds row0916 row0917 = true := by
  decide +kernel

theorem transition0917 : transitionRowCheck seeds row0917 row0918 = true := by
  decide +kernel

theorem transition0918 : transitionRowCheck seeds row0918 row0919 = true := by
  decide +kernel

theorem transition0919 : transitionRowCheck seeds row0919 row0920 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
