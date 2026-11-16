/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile09Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile09Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (506321/524288 : ℚ), (-12440385567809275957054364285496)⟩

theorem profile09Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨9, by decide⟩) (2*approximationError) profile09Join02_0005Claim :=
  profile09Join01_0010Bound.glue profile09Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
