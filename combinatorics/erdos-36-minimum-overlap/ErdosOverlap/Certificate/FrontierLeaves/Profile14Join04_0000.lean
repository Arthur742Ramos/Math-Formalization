/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join03_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile14Join03_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile14Join04_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (9289/14276 : ℚ), 37015757262287936144551146055462⟩

theorem profile14Join04_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨14, by decide⟩) (2*approximationError) profile14Join04_0000Claim :=
  profile14Join03_0000Bound.glue profile14Join03_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
