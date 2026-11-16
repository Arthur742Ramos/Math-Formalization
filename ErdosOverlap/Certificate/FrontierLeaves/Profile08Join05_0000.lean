/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 20487296944101438137417589932866⟩

theorem profile08Join05_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join05_0000Claim :=
  profile08Join04_0000Bound.glue profile08Join04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
