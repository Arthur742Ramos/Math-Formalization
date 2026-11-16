/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile17Join00_0001Claim : IntegralClaim := ⟨(583/262144 : ℚ), (4749/1048576 : ℚ), 0⟩

theorem profile17Join00_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join00_0001Claim :=
  profile17Block0002.glue profile17Block0003 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
