/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join01_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join02_0003Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (9289/14276 : ℚ), 12761037738574400296447070536214⟩

theorem profile14Join02_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join02_0003Claim :=
  profile14Join01_0006Bound.glue profile14Join01_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
