/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0000
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin01_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin02_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (106311/241664 : ℚ), 28301110864240284798205223132866⟩

theorem centralJoin02_0000Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin02_0000Claim :=
  centralJoin01_0000Bound.glue centralJoin01_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
