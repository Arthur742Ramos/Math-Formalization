/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0016
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join00_0008Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (6579/262144 : ℚ), 0⟩

theorem profile14Join00_0008Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0008Claim :=
  profile14Block0016.glue profile14Block0017 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
