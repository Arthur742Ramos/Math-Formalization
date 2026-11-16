/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0016
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0017

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join00_0008Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (6579/262144 : ℚ), 0⟩

theorem profile10Join00_0008Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join00_0008Claim :=
  profile10Block0016.glue profile10Block0017 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
