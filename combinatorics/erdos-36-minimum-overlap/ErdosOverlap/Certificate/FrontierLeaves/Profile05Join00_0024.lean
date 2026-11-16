/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0024Claim : IntegralClaim := ⟨(128771/131072 : ℚ), (64757/65536 : ℚ), (-2912861616902289572951491440519)⟩

theorem profile05Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join00_0024Claim :=
  profile05Block0048.glue profile05Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
