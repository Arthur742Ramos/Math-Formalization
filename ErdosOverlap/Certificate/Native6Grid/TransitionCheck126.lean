module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows126
public import ErdosOverlap.Certificate.Native6Grid.Rows127

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition1008 : transitionRowCheck seeds row1008 row1009 = true := by
  decide +kernel

theorem transition1009 : transitionRowCheck seeds row1009 row1010 = true := by
  decide +kernel

theorem transition1010 : transitionRowCheck seeds row1010 row1011 = true := by
  decide +kernel

theorem transition1011 : transitionRowCheck seeds row1011 row1012 = true := by
  decide +kernel

theorem transition1012 : transitionRowCheck seeds row1012 row1013 = true := by
  decide +kernel

theorem transition1013 : transitionRowCheck seeds row1013 row1014 = true := by
  decide +kernel

theorem transition1014 : transitionRowCheck seeds row1014 row1015 = true := by
  decide +kernel

theorem transition1015 : transitionRowCheck seeds row1015 row1016 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
