/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0022
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join00_0023

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile09Join01_0011Claim : IntegralClaim := ⟨(135183/145408 : ℚ), (506321/524288 : ℚ), (-12440385567809275957054364285496)⟩

theorem profile09Join01_0011Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join01_0011Claim :=
  profile09Join00_0022Bound.glue profile09Join00_0023Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
