/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile19Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (16265/16384 : ℚ), (-3158130968766795795794174846)⟩

theorem profile19Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join00_0023Claim :=
  profile19Block0046.glue profile19Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
