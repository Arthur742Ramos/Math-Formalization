/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join01_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join01_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join02_0001Claim : IntegralClaim := ⟨(319/32768 : ℚ), (11173/524288 : ℚ), 0⟩

theorem profile12Join02_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join02_0001Claim :=
  profile12Join01_0002Bound.glue profile12Join01_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
