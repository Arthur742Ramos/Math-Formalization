/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0048
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0049

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile13Join00_0024Claim : IntegralClaim := ⟨(1034617/1048576 : ℚ), (65229/65536 : ℚ), (-9860706045022768911912462159)⟩

theorem profile13Join00_0024Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0024Claim :=
  profile13Block0048.glue profile13Block0049 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
