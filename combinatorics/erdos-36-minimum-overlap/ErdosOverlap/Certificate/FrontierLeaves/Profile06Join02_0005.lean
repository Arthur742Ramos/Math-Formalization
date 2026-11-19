/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile06Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile06Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (128259/131072 : ℚ), (-4623498562819373509662099201201)⟩

theorem profile06Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨6, by decide⟩) (2*approximationError) profile06Join02_0005Claim :=
  profile06Join01_0010Bound.glue profile06Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
