/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile19Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (16265/16384 : ℚ), (-3158130968766795795794174846)⟩

theorem profile19Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join01_0011Claim :=
  profile19Join00_0022Bound.glue profile19Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
