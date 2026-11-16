/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join05_0000

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile19Claim : IntegralClaim := profile19Join05_0000Claim

theorem profile19Certificate : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Claim :=
  profile19Join05_0000Bound

end
end ErdosOverlap.FrontierLeaves
