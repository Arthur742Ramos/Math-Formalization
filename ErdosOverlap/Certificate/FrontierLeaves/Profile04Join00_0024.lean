/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join00_0024Claim : IntegralClaim := ⟨(2017/2048 : ℚ), (519729/524288 : ℚ), (-2901539102285825272086139189800)⟩

theorem profile04Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0024Claim :=
  profile04Block0048.glue profile04Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
