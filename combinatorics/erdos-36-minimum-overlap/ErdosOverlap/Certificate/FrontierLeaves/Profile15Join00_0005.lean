/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join00_0005Claim : IntegralClaim := ⟨(12941/1048576 : ℚ), (15667/1048576 : ℚ), 0⟩

theorem profile15Join00_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0005Claim :=
  profile15Block0010.glue profile15Block0011 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
