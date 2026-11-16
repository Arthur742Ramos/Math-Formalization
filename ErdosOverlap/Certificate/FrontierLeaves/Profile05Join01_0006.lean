/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join00_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join01_0006Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (1633327/3178496 : ℚ), 10128885579697731028934869622830⟩

theorem profile05Join01_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join01_0006Claim :=
  profile05Join00_0012Bound.glue profile05Join00_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
