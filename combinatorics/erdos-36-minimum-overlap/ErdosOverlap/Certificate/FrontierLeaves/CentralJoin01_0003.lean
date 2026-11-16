/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0006
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin01_0003Claim : IntegralClaim := ⟨(2879/5080 : ℚ), (88033/131072 : ℚ), 1641305022601149051560803530479⟩

theorem centralJoin01_0003Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0003Claim :=
  centralJoin00_0006Bound.glue centralJoin00_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
