/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (63943/65536 : ℚ), (-5401101591328017047823220939517)⟩

theorem profile07Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join01_0011Claim :=
  profile07Join00_0022Bound.glue profile07Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
