/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (128259/131072 : ℚ), (-4623498562819373509662099201201)⟩

theorem profile06Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join01_0011Claim :=
  profile06Join00_0022Bound.glue profile06Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
