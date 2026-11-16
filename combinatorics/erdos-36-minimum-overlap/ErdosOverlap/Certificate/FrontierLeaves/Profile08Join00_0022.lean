/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (63209/65536 : ℚ), (-2103868514053506258327821849503)⟩

theorem profile08Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0022Claim :=
  profile08Block0044.glue profile08Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
