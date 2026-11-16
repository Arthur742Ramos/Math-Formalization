/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join01_0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join01_0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join02_0006Claim : IntegralClaim := ⟨(506321/524288 : ℚ), (4128705/4161536 : ℚ), (-12695243873680747974025894531052)⟩

theorem profile09Join02_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join02_0006Claim :=
  profile09Join01_0012Bound.glue profile09Join01_0013Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
