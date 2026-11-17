/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join00_0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join00_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile16Join01_0003Claim : IntegralClaim := ⟨(15667/1048576 : ℚ), (11173/524288 : ℚ), 0⟩

theorem profile16Join01_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join01_0003Claim :=
  profile16Join00_0006Bound.glue profile16Join00_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
