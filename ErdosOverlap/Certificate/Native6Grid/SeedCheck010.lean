module

public import ErdosOverlap.Certificate.Native6Grid.Seeds02

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem seedCheck010 : rotationSeedsCheck ((seeds02.drop 32).take 16) = true := by
  decide +kernel

end
end ErdosOverlap.Native6Grid
