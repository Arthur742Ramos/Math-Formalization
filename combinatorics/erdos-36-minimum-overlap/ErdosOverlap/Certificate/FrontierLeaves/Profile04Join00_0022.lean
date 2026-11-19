/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0044
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Block0045

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join00_0022Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (16037/16384 : ℚ), (-30238769751890153754355449276)⟩

theorem profile04Join00_0022Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join00_0022Claim :=
  profile04Block0044.glue profile04Block0045 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
