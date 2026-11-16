/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0018
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0019

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join00_0009Claim : IntegralClaim := ⟨(6579/262144 : ℚ), (7685/262144 : ℚ), 0⟩

theorem profile17Join00_0009Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join00_0009Claim :=
  profile17Block0018.glue profile17Block0019 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
