/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join00_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join00_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join01_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (4749/1048576 : ℚ), 0⟩

theorem profile18Join01_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join01_0000Claim :=
  profile18Join00_0000Bound.glue profile18Join00_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
