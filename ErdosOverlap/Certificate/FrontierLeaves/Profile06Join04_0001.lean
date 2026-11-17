/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join02_0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), (-11483035566076317682114508531004)⟩

theorem profile06Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join04_0001Claim :=
  profile06Join03_0002Bound.glue profile06Join02_0006Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
