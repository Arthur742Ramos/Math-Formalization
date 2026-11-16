/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.DenominatorJoin06_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def denominatorClaim : IntegralClaim := denominatorJoin06_0000Claim

theorem denominatorCertificate : IntegralClaim.UpperCertificate denominatorIntegrand (4*approximationError) denominatorClaim :=
  denominatorJoin06_0000Bound

end
end ErdosOverlap.FrontierLeaves
