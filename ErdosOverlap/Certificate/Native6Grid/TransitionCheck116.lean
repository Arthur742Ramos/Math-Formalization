module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows116
public import ErdosOverlap.Certificate.Native6Grid.Rows117

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0928 : transitionRowCheck seeds row0928 row0929 = true := by
  decide +kernel

theorem transition0929 : transitionRowCheck seeds row0929 row0930 = true := by
  decide +kernel

theorem transition0930 : transitionRowCheck seeds row0930 row0931 = true := by
  decide +kernel

theorem transition0931 : transitionRowCheck seeds row0931 row0932 = true := by
  decide +kernel

theorem transition0932 : transitionRowCheck seeds row0932 row0933 = true := by
  decide +kernel

theorem transition0933 : transitionRowCheck seeds row0933 row0934 = true := by
  decide +kernel

theorem transition0934 : transitionRowCheck seeds row0934 row0935 = true := by
  decide +kernel

theorem transition0935 : transitionRowCheck seeds row0935 row0936 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
