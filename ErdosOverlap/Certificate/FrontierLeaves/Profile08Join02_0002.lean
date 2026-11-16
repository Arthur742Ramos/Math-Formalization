/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join02_0002Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (52715/131072 : ℚ), 24254719523713535848104075519248⟩

theorem profile08Join02_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join02_0002Claim :=
  profile08Join01_0004Bound.glue profile08Join01_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
