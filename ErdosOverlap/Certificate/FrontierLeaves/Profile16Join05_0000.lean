/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile16Join05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 38003305133985989339995736293792⟩

theorem profile16Join05_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join05_0000Claim :=
  profile16Join04_0000Bound.glue profile16Join04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
