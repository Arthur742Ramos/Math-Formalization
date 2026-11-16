/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (16269/16384 : ℚ), 991652396957417963212361338658⟩

theorem profile14Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join03_0002Claim :=
  profile14Join02_0004Bound.glue profile14Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
