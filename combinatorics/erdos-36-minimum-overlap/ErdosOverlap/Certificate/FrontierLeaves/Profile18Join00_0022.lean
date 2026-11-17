/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile18Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (8023/8192 : ℚ), 0⟩

theorem profile18Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0022Claim :=
  profile18Block0044.glue profile18Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
