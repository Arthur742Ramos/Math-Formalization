/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile13Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (1034617/1048576 : ℚ), (-3198578555263409330700250197)⟩

theorem profile13Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join01_0011Claim :=
  profile13Join00_0022Bound.glue profile13Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
