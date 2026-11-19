/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile05Join00_0023Claim : IntegralClaim := ⟨(16252565/16646144 : ℚ), (128771/131072 : ℚ), (-2910520113039610682880254989706)⟩

theorem profile05Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join00_0023Claim :=
  profile05Block0046.glue profile05Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
