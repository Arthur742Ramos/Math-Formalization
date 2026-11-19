/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Join01_0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Join01_0007

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile11Join02_0003Claim : IntegralClaim := ⟨(52715/131072 : ℚ), (9289/14276 : ℚ), 12761037738574400296447070536214⟩

theorem profile11Join02_0003Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Join02_0003Claim :=
  profile11Join01_0006Bound.glue profile11Join01_0007Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
