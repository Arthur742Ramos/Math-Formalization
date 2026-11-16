/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join00_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join00_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join01_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (4749/1048576 : ℚ), 0⟩

theorem profile15Join01_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join01_0000Claim :=
  profile15Join00_0000Bound.glue profile15Join00_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
