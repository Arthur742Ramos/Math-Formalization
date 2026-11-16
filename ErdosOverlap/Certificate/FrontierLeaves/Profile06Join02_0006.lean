/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join00_0026
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join01_0012

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile06Join02_0006Claim : IntegralClaim := ⟨(128259/131072 : ℚ), (1/1 : ℚ), (-7854351244596906192097686826811)⟩

theorem profile06Join02_0006Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join02_0006Claim :=
  profile06Join01_0012Bound.glue profile06Join00_0026Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
