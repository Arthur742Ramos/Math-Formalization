/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0004
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def centralJoin02_0002Claim : IntegralClaim := ⟨(88033/131072 : ℚ), (29737/32768 : ℚ), 477325373021996425421100970836⟩

theorem centralJoin02_0002Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin02_0002Claim :=
  centralJoin01_0004Bound.glue centralJoin01_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
