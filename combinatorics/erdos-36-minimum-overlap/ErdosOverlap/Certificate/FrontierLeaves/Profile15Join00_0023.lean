/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (260211/262144 : ℚ), (-3276373683945557213743660404)⟩

theorem profile15Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0023Claim :=
  profile15Block0046.glue profile15Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
