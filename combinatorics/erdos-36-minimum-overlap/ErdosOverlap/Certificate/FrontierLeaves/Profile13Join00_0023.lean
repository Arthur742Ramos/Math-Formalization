/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile13Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile13Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (1034617/1048576 : ℚ), (-3198578555263409330700250197)⟩

theorem profile13Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨13, by decide⟩) (2*approximationError) profile13Join00_0023Claim :=
  profile13Block0046.glue profile13Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
