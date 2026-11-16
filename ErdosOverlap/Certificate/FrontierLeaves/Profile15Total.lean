/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Join05_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile15Claim : IntegralClaim := profile15Join05_0000Claim

theorem profile15Certificate : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Claim :=
  profile15Join05_0000Bound

end
end ErdosOverlap.FrontierLeaves
