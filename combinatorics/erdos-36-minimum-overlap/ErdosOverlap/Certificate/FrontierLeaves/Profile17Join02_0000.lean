/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join01_0000
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join01_0001

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join02_0000Claim : IntegralClaim := ⟨(0/1 : ℚ), (319/32768 : ℚ), 0⟩

theorem profile17Join02_0000Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join02_0000Claim :=
  profile17Join01_0000Bound.glue profile17Join01_0001Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
