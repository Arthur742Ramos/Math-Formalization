/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (16252565/16646144 : ℚ), (-490466645375330514665254236358)⟩

theorem profile05Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join00_0022Claim :=
  profile05Block0044.glue profile05Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
