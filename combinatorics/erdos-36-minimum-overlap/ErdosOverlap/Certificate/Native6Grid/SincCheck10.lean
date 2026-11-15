module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower10 : ℚ := (-11/10000000000000000 : ℚ)

theorem sincCheck10 :
    (sincSumBox Native6Trig.chunk10).lowerBoundedBy sincLower10 = true := by
  decide +kernel

theorem sincLower10_le : (sincLower10 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk10 :=
  sincSum_lower_of_check _ _ sincCheck10

end
end ErdosOverlap.Native6Grid
