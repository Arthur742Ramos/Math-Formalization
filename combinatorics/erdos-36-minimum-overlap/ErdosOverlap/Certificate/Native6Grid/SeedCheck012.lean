module

public import ErdosOverlap.Certificate.Native6Grid.Seeds03

namespace ErdosOverlap.Native6Grid
open Numerics
public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

theorem seedCheck012 : rotationSeedsCheck (seeds03.take 16) = true := by
  decide +kernel

end
end ErdosOverlap.Native6Grid
