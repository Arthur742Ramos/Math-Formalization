/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (130089/131072 : ℚ), (-3369977987537717914546714999)⟩

theorem profile12Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join00_0023Claim :=
  profile12Block0046.glue profile12Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
