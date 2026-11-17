/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0032
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Block0033

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join00_0016Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (175441/262144 : ℚ), 304316046342492473122696854297⟩

theorem profile09Join00_0016Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join00_0016Claim :=
  profile09Block0032.glue profile09Block0033 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
