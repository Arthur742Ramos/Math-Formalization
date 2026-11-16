/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0024Claim : IntegralClaim := ⟨(128259/131072 : ℚ), (129043/131072 : ℚ), (-2869777437624848871716449262827)⟩

theorem profile06Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0024Claim :=
  profile06Block0048.glue profile06Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
