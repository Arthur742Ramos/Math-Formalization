module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower08 : ℚ := (-2223/2500000000000000 : ℚ)

theorem sincCheck08 :
    (sincSumBox Native6Trig.chunk08).lowerBoundedBy sincLower08 = true := by
  decide +kernel

theorem sincLower08_le : (sincLower08 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk08 :=
  sincSum_lower_of_check _ _ sincCheck08

end
end ErdosOverlap.Native6Grid
