/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0008
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join00_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join01_0004Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (7685/262144 : ℚ), 0⟩

theorem profile08Join01_0004Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join01_0004Claim :=
  profile08Join00_0008Bound.glue profile08Join00_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
