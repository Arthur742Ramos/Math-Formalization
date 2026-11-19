/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join02_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join03_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (11173/524288 : ℚ), 0⟩

theorem profile17Join03_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join03_0000Claim :=
  profile17Join02_0000Bound.glue profile17Join02_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
