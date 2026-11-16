/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0025Claim : IntegralClaim := ⟨(129043/131072 : ℚ), (129861/131072 : ℚ), (-2954488672243062803760907966946)⟩

theorem profile06Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0025Claim :=
  profile06Block0050.glue profile06Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
