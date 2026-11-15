module

public import ErdosOverlap.Certificate.Native6Grid.Seeds
public import ErdosOverlap.Certificate.Native6Grid.Rows026
public import ErdosOverlap.Certificate.Native6Grid.Rows027

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem transition0208 : transitionRowCheck seeds row0208 row0209 = true := by
  decide +kernel

theorem transition0209 : transitionRowCheck seeds row0209 row0210 = true := by
  decide +kernel

theorem transition0210 : transitionRowCheck seeds row0210 row0211 = true := by
  decide +kernel

theorem transition0211 : transitionRowCheck seeds row0211 row0212 = true := by
  decide +kernel

theorem transition0212 : transitionRowCheck seeds row0212 row0213 = true := by
  decide +kernel

theorem transition0213 : transitionRowCheck seeds row0213 row0214 = true := by
  decide +kernel

theorem transition0214 : transitionRowCheck seeds row0214 row0215 = true := by
  decide +kernel

theorem transition0215 : transitionRowCheck seeds row0215 row0216 = true := by
  decide +kernel


end
end ErdosOverlap.Native6Grid
