/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (63707/65536 : ℚ), (-826209633683329596721954122741)⟩

theorem profile06Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0022Claim :=
  profile06Block0044.glue profile06Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
