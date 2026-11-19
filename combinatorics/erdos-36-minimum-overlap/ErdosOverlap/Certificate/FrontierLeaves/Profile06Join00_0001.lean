/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Block0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join00_0001Claim : IntegralClaim := ⟨(583/262144 : ℚ), (4749/1048576 : ℚ), 0⟩

theorem profile06Join00_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join00_0001Claim :=
  profile06Block0002.glue profile06Block0003 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
