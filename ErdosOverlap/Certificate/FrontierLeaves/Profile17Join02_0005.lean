/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (130101/131072 : ℚ), (-3343397427152145384632872031)⟩

theorem profile17Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join02_0005Claim :=
  profile17Join01_0010Bound.glue profile17Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
