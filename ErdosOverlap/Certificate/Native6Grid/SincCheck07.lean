module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower07 : ℚ := (-110093/10000000000000000 : ℚ)

theorem sincCheck07 :
    (sincSumBox Native6Trig.chunk07).lowerBoundedBy sincLower07 = true := by
  decide +kernel

theorem sincLower07_le : (sincLower07 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk07 :=
  sincSum_lower_of_check _ _ sincCheck07

end
end ErdosOverlap.Native6Grid
