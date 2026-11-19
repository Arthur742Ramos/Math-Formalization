/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (130101/131072 : ℚ), (-3343397427152145384632872031)⟩

theorem profile17Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join00_0023Claim :=
  profile17Block0046.glue profile17Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
