module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower09 : ℚ := (-2553/10000000000000000 : ℚ)

theorem sincCheck09 :
    (sincSumBox Native6Trig.chunk09).lowerBoundedBy sincLower09 = true := by
  decide +kernel

theorem sincLower09_le : (sincLower09 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk09 :=
  sincSum_lower_of_check _ _ sincCheck09

end
end ErdosOverlap.Native6Grid
