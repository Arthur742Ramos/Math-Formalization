/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0025

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join01_0012Claim : IntegralClaim := ⟨(128259/131072 : ℚ), (129861/131072 : ℚ), (-5824266109867911675477357229773)⟩

theorem profile06Join01_0012Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join01_0012Claim :=
  profile06Join00_0024Bound.glue profile06Join00_0025Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
