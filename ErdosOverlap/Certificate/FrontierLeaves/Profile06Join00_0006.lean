/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0006Claim : IntegralClaim := ⟨(15667/1048576 : ℚ), (2329/131072 : ℚ), 0⟩

theorem profile06Join00_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0006Claim :=
  profile06Block0012.glue profile06Block0013 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
