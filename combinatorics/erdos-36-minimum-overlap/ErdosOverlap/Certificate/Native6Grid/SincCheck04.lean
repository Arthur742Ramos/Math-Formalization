module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower04 : ℚ := (-264477/1250000000000000 : ℚ)

theorem sincCheck04 :
    (sincSumBox Native6Trig.chunk04).lowerBoundedBy sincLower04 = true := by
  decide +kernel

theorem sincLower04_le : (sincLower04 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk04 :=
  sincSum_lower_of_check _ _ sincCheck04

end
end ErdosOverlap.Native6Grid
