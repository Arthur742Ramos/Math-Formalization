/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile11Join00_0011Claim : IntegralClaim := ⟨(327871/1048576 : ℚ), (52715/131072 : ℚ), 16896769620083106515720042929495⟩

theorem profile11Join00_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Join00_0011Claim :=
  profile11Block0022.glue profile11Block0023 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
