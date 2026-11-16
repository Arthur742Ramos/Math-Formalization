/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (1034617/1048576 : ℚ), 991615662784698610314577246811⟩

theorem profile13Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join03_0002Claim :=
  profile13Join02_0004Bound.glue profile13Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
