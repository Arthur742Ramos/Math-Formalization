/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Block0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile19Join00_0006Claim : IntegralClaim := ⟨(15667/1048576 : ℚ), (2329/131072 : ℚ), 0⟩

theorem profile19Join00_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join00_0006Claim :=
  profile19Block0012.glue profile19Block0013 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
