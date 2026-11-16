/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0052
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0053

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0026Claim : IntegralClaim := ⟨(129861/131072 : ℚ), (1/1 : ℚ), (-2030085134728994516620329597038)⟩

theorem profile06Join00_0026Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0026Claim :=
  profile06Block0052.glue profile06Block0053 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
