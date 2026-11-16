/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join01_0010
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join01_0011

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join02_0005Claim : IntegralClaim := ⟨(54239/65536 : ℚ), (1034617/1048576 : ℚ), (-3198578555263409330700250197)⟩

theorem profile13Join02_0005Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join02_0005Claim :=
  profile13Join01_0010Bound.glue profile13Join01_0011Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
