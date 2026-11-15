module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower01 : ℚ := (-22116279/5000000000000000 : ℚ)

theorem sincCheck01 :
    (sincSumBox Native6Trig.chunk01).lowerBoundedBy sincLower01 = true := by
  decide +kernel

theorem sincLower01_le : (sincLower01 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk01 :=
  sincSum_lower_of_check _ _ sincCheck01

end
end ErdosOverlap.Native6Grid
