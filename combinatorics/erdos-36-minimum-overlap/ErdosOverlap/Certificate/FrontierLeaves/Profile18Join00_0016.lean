/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0032
public import ErdosOverlap.Certificate.FrontierLeaves.Profile18Block0033

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile18Join00_0016Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (175441/262144 : ℚ), 304316046342492473122696854297⟩

theorem profile18Join00_0016Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨18, by decide⟩) (2*approximationError) profile18Join00_0016Claim :=
  profile18Block0032.glue profile18Block0033 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
