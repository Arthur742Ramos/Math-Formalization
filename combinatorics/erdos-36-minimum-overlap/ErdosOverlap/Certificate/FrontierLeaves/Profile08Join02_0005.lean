/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile08Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (127357/131072 : ℚ), (-5657862758686410951426056300109)⟩

theorem profile08Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join02_0005Claim :=
  profile08Join01_0010Bound.glue profile08Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
