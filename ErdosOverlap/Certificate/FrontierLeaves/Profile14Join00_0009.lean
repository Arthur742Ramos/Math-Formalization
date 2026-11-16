/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0018
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Block0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join00_0009Claim : IntegralClaim := ⟨(6579/262144 : ℚ), (7685/262144 : ℚ), 0⟩

theorem profile14Join00_0009Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join00_0009Claim :=
  profile14Block0018.glue profile14Block0019 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
