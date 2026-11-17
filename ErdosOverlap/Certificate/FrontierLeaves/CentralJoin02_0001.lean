/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0002
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin02_0001Claim : IntegralClaim := ⟨(106311/241664 : ℚ), (88033/131072 : ℚ), 9231414810058855618664837919093⟩

theorem centralJoin02_0001Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin02_0001Claim :=
  centralJoin01_0002Bound.glue centralJoin01_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
