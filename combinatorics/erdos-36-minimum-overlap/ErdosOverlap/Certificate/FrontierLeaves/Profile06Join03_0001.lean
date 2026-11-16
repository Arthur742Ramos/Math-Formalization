/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join02_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join02_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join03_0001Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (9289/14276 : ℚ), 37015757262287936144551146055462⟩

theorem profile06Join03_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join03_0001Claim :=
  profile06Join02_0002Bound.glue profile06Join02_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
