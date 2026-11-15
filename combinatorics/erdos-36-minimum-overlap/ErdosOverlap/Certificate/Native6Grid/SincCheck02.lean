module

public import ErdosOverlap.Numerics.SincEnclosure
public import ErdosOverlap.Certificate.Native6TrigData

namespace ErdosOverlap.Native6Grid
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def sincLower02 : ℚ := (-2167719/1000000000000000 : ℚ)

theorem sincCheck02 :
    (sincSumBox Native6Trig.chunk02).lowerBoundedBy sincLower02 = true := by
  decide +kernel

theorem sincLower02_le : (sincLower02 : ℝ) ≤ Native6.cosineLower Native6Trig.chunk02 :=
  sincSum_lower_of_check _ _ sincCheck02

end
end ErdosOverlap.Native6Grid
