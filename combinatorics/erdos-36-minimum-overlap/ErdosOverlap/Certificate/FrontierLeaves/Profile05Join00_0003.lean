/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0003Claim : IntegralClaim := ⟨(1871/262144 : ℚ), (319/32768 : ℚ), 0⟩

theorem profile05Join00_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join00_0003Claim :=
  profile05Block0006.glue profile05Block0007 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
