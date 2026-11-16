/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join04_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join04_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join05_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (1/1 : ℚ), 38003367250415009210942782935547⟩

theorem profile17Join05_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join05_0000Claim :=
  profile17Join04_0000Bound.glue profile17Join04_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
