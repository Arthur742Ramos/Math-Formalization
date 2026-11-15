module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower03 : ℚ := (-988661/2000000000000000 : ℚ)

theorem sincCheck03 :
    (sincSumBox Native6Trig.chunk03).lowerBoundedBy sincLower03 = true := by
  decide +kernel

theorem sincLower03_le : (sincLower03 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk03 :=
  sincSum_lower_of_check _ _ sincCheck03

end
end ErdosOverlap.Native6Grid
