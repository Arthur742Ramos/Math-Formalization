/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (127357/131072 : ℚ), (-5657862758686410951426056300109)⟩

theorem profile08Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join01_0011Claim :=
  profile08Join00_0022Bound.glue profile08Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
