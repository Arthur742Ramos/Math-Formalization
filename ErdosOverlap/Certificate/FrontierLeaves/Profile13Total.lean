/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join05_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Claim : IntegralClaim := profile13Join05_0000Claim

theorem profile13Certificate : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Claim :=
  profile13Join05_0000Bound

end
end ErdosOverlap.FrontierLeaves
