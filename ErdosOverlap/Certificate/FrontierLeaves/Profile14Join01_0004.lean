/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join00_0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join00_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join01_0004Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (7685/262144 : ℚ), 0⟩

theorem profile14Join01_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join01_0004Claim :=
  profile14Join00_0008Bound.glue profile14Join00_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
