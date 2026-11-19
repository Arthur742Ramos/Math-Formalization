/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin02_0000
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin02_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin03_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (88033/131072 : ℚ), 37532525674299140416870061051959⟩

theorem centralJoin03_0000Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin03_0000Claim :=
  centralJoin02_0000Bound.glue centralJoin02_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
