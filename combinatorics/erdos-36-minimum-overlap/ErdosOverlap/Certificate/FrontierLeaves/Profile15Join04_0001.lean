/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), 987732056763943046367503136440⟩

theorem profile15Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join04_0001Claim :=
  profile15Join03_0002Bound.glue profile15Join00_0024Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
