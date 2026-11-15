module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower05 : ℚ := (-6247/250000000000000 : ℚ)

theorem sincCheck05 :
    (sincSumBox Native6Trig.chunk05).lowerBoundedBy sincLower05 = true := by
  decide +kernel

theorem sincLower05_le : (sincLower05 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk05 :=
  sincSum_lower_of_check _ _ sincCheck05

end
end ErdosOverlap.Native6Grid
