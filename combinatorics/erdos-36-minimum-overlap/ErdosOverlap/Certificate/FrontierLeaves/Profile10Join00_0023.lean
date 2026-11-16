/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (4059/4096 : ℚ), (-3201208064343582036509040950)⟩

theorem profile10Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join00_0023Claim :=
  profile10Block0046.glue profile10Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
