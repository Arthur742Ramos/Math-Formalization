/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join00_0024
public import ErdosOverlap.Certificate.FrontierLeaves.Profile19Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile19Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), 987894567410845427758150888727⟩

theorem profile19Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨19, by decide⟩) (2*approximationError) profile19Join04_0001Claim :=
  profile19Join03_0002Bound.glue profile19Join00_0024Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
