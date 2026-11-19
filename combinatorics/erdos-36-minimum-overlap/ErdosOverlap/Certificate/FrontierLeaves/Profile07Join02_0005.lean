/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable def profile07Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (63943/65536 : ℚ), (-5401101591328017047823220939517)⟩

theorem profile07Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join02_0005Claim :=
  profile07Join01_0010Bound.glue profile07Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
