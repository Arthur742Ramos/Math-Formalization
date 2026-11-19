/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0002
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0003

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join03_0001Claim : IntegralClaim := ⟨(11173/524288 : ℚ), (9289/14276 : ℚ), 37015757262287936144551146055462⟩

theorem profile17Join03_0001Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join03_0001Claim :=
  profile17Join02_0002Bound.glue profile17Join02_0003Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
