/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join02_0001Claim : IntegralClaim := ⟨(319/32768 : ℚ), (11173/524288 : ℚ), 0⟩

theorem profile14Join02_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join02_0001Claim :=
  profile14Join01_0002Bound.glue profile14Join01_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
