/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (126885/131072 : ℚ), (-1610126185626639966823685939372)⟩

theorem profile07Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0022Claim :=
  profile07Block0044.glue profile07Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
