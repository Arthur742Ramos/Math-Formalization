/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0008
public import ErdosOverlap.Certificate.FrontierLeaves.CentralJoin00_0009

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def centralJoin01_0004Claim : IntegralClaim := ⟨(88033/131072 : ℚ), (786621/999424 : ℚ), 477325373021996425421100970836⟩

theorem centralJoin01_0004Bound : IntegralClaim.LowerCertificate centralIntegrand (2*approximationError) centralJoin01_0004Claim :=
  centralJoin00_0008Bound.glue centralJoin00_0009Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
