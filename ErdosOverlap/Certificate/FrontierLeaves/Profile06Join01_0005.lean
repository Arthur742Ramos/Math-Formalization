/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join01_0005Claim : IntegralClaim := ⟨(7685/262144 : ℚ), (52715/131072 : ℚ), 24254719523713535848104075519248⟩

theorem profile06Join01_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join01_0005Claim :=
  profile06Join00_0010Bound.glue profile06Join00_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
