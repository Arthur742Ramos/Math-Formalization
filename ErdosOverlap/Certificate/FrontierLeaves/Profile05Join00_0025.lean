/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0050
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0051

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join00_0025Claim : IntegralClaim := ⟨(64757/65536 : ℚ), (130581/131072 : ℚ), (-1428677659310603581643839447893)⟩

theorem profile05Join00_0025Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join00_0025Claim :=
  profile05Block0050.glue profile05Block0051 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
