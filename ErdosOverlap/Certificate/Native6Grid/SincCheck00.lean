module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower00 : ℚ := (-341250768651/5000000000000000 : ℚ)

theorem sincCheck00 :
    (sincSumBox Native6Trig.chunk00).lowerBoundedBy sincLower00 = true := by
  decide +kernel

theorem sincLower00_le : (sincLower00 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk00 :=
  sincSum_lower_of_check _ _ sincCheck00

end
end ErdosOverlap.Native6Grid
