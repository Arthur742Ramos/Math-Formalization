/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0018
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join00_0009Claim : IntegralClaim := ⟨(6579/262144 : ℚ), (7685/262144 : ℚ), 0⟩

theorem profile18Join00_0009Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0009Claim :=
  profile18Block0018.glue profile18Block0019 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
