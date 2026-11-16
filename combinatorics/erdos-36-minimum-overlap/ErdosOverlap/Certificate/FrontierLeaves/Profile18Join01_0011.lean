/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (16263/16384 : ℚ), (-3282415963184493672586785615)⟩

theorem profile18Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join01_0011Claim :=
  profile18Join00_0022Bound.glue profile18Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
