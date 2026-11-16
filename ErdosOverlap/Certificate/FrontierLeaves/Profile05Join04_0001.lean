/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join02_0006
public import ErdosOverlap.Certificate.FrontierLeaves.Profile05Join03_0002

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile05Join04_0001Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1/1 : ℚ), (-8502937007732078847074240922287)⟩

theorem profile05Join04_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨5, by decide⟩) (2*approximationError) profile05Join04_0001Claim :=
  profile05Join03_0002Bound.glue profile05Join02_0006Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
