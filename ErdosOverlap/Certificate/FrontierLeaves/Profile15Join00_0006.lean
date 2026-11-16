/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0012
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0013

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join00_0006Claim : IntegralClaim := ⟨(15667/1048576 : ℚ), (2329/131072 : ℚ), 0⟩

theorem profile15Join00_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0006Claim :=
  profile15Block0012.glue profile15Block0013 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
