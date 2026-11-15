module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower06 : ℚ := (-170723/10000000000000000 : ℚ)

theorem sincCheck06 :
    (sincSumBox Native6Trig.chunk06).lowerBoundedBy sincLower06 = true := by
  decide +kernel

theorem sincLower06_le : (sincLower06 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk06 :=
  sincSum_lower_of_check _ _ sincCheck06

end
end ErdosOverlap.Native6Grid
