/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join02_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (319/32768 : ℚ), 0⟩

theorem profile08Join02_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join02_0000Claim :=
  profile08Join01_0000Bound.glue profile08Join01_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
