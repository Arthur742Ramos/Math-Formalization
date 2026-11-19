/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0006
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin02_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin03_0001Claim : IntegralClaim := ⟨(88033/131072 : ℚ), (1/1 : ℚ), 477325373021996425421100970836⟩

theorem centralJoin03_0001Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin03_0001Claim :=
  centralJoin02_0002Bound.glue centralJoin01_0006Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
