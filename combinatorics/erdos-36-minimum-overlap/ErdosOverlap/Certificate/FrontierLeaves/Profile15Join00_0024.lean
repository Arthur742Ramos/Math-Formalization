/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile15Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile15Join00_0024Claim : IntegralClaim := ⟨(260211/262144 : ℚ), (1/1 : ℚ), (-3805810892073416064030700164)⟩

theorem profile15Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨15, by decide⟩) (2*approximationError) profile15Join00_0024Claim :=
  profile15Block0048.glue profile15Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
