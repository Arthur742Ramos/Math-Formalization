/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile16Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (8023/8192 : ℚ), 0⟩

theorem profile16Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join00_0022Claim :=
  profile16Block0044.glue profile16Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
