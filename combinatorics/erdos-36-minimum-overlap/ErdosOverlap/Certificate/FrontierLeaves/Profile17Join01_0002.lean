/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile17Join00_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile17Join01_0002Claim : IntegralClaim := ⟨(319/32768 : ℚ), (15667/1048576 : ℚ), 0⟩

theorem profile17Join01_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨17, by decide⟩) (2*approximationError) profile17Join01_0002Claim :=
  profile17Join00_0004Bound.glue profile17Join00_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
