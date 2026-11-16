/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (260211/262144 : ℚ), (-3276373683945557213743660404)⟩

theorem profile15Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join02_0005Claim :=
  profile15Join01_0010Bound.glue profile15Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
