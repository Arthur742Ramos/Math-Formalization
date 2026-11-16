/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile04Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile04Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (2017/2048 : ℚ), (-2908100326212737328542825406433)⟩

theorem profile04Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨4, by decide⟩) (2*approximationError) profile04Join02_0005Claim :=
  profile04Join01_0010Bound.glue profile04Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
