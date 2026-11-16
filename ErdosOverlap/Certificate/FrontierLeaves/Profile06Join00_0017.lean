/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0034
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0035

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0017Claim : IntegralClaim := ⟨(175441/262144 : ℚ), (1469/2048 : ℚ), 577686278291183560307924963535⟩

theorem profile06Join00_0017Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0017Claim :=
  profile06Block0034.glue profile06Block0035 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
