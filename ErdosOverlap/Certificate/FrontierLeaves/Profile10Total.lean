/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join05_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Claim : IntegralClaim := profile10Join05_0000Claim

theorem profile10Certificate : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Claim :=
  profile10Join05_0000Bound

end
end ErdosOverlap.FrontierLeaves
