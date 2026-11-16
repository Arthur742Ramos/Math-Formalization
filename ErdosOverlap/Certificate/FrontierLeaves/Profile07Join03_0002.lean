/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile07Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile07Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (63943/65536 : ℚ), (-4406287349988055028177943442509)⟩

theorem profile07Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨7, by decide⟩) (2*approximationError) profile07Join03_0002Claim :=
  profile07Join02_0004Bound.glue profile07Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
