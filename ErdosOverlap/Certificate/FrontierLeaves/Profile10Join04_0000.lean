/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join03_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join03_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join04_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (9289/14276 : ℚ), 37015757262287936144551146055462⟩

theorem profile10Join04_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join04_0000Claim :=
  profile10Join03_0000Bound.glue profile10Join03_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
