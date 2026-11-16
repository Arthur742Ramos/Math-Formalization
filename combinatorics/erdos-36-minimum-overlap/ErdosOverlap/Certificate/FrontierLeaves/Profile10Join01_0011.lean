/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (4059/4096 : ℚ), (-3201208064343582036509040950)⟩

theorem profile10Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join01_0011Claim :=
  profile10Join00_0022Bound.glue profile10Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
