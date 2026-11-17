/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile04Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (2017/2048 : ℚ), (-2908100326212737328542825406433)⟩

theorem profile04Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join01_0011Claim :=
  profile04Join00_0022Bound.glue profile04Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
