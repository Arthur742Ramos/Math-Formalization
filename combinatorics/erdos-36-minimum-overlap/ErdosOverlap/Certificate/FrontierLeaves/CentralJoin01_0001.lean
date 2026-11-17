/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0002
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin01_0001Claim : IntegralClaim := ⟨(39/256 : ℚ), (106311/241664 : ℚ), 28301110864240284798205223132866⟩

theorem centralJoin01_0001Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0001Claim :=
  centralJoin00_0002Bound.glue centralJoin00_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
