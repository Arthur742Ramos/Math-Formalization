/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (128259/131072 : ℚ), (-3628684321479411490016821704193)⟩

theorem profile06Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join03_0002Claim :=
  profile06Join02_0004Bound.glue profile06Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
