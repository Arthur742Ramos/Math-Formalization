/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join00_0024Claim : IntegralClaim := ⟨(16263/16384 : ℚ), (1/1 : ℚ), (-3860855800896865539027592453)⟩

theorem profile18Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0024Claim :=
  profile18Block0048.glue profile18Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
