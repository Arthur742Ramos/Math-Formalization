/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (130101/131072 : ℚ), (-3343397427152145384632872031)⟩

theorem profile17Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join01_0011Claim :=
  profile17Join00_0022Bound.glue profile17Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
