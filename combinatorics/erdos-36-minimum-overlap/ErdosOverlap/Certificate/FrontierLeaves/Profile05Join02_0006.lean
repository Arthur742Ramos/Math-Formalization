/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Block0052
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join01_0012

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile05Join02_0006Claim : IntegralClaim := ⟨(128771/131072 : ℚ), (1/1 : ℚ), (-6096764490657099669174009193231)⟩

theorem profile05Join02_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join02_0006Claim :=
  profile05Join01_0012Bound.glue profile05Block0052 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
