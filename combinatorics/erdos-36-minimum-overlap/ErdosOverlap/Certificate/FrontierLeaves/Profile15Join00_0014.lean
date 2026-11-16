/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0028
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0029

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join00_0014Claim : IntegralClaim := ⟨(1633327/3178496 : ℚ), (77107/131072 : ℚ), 1814321690190131858533385752969⟩

theorem profile15Join00_0014Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0014Claim :=
  profile15Block0028.glue profile15Block0029 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
