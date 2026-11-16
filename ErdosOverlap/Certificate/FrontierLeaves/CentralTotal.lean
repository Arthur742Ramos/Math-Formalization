/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin04_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralClaim : IntegralClaim := centralJoin04_0000Claim

theorem centralCertificate : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralClaim :=
  centralJoin04_0000Bound

end
end ErdosOverlap.FrontierLeaves
