/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join00_0024Claim : IntegralClaim := ⟨(63943/65536 : ℚ), (514723/524288 : ℚ), (-2961053247006211552342276622537)⟩

theorem profile07Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join00_0024Claim :=
  profile07Block0048.glue profile07Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
