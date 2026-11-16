/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0046
public import ErdosOverlap.Certificate.FrontierLeaves.Profile11Block0047

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile11Join00_0023Claim : IntegralClaim := ⟨(8023/8192 : ℚ), (130329/131072 : ℚ), (-3482608070359730633523502897)⟩

theorem profile11Join00_0023Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨11, by decide⟩) (2*approximationError) profile11Join00_0023Claim :=
  profile11Block0046.glue profile11Block0047 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
