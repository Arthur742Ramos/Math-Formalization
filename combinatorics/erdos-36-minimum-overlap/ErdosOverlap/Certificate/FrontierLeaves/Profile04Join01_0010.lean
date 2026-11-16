/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0020
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0021

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join01_0010Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (135183/145408 : ℚ), 0⟩

theorem profile04Join01_0010Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join01_0010Claim :=
  profile04Join00_0020Bound.glue profile04Join00_0021Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
