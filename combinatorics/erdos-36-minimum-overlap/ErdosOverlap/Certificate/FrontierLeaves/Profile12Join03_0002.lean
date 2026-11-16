/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile12Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile12Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (130089/131072 : ℚ), 991444263352424301730730782009⟩

theorem profile12Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨12, by decide⟩) (2*approximationError) profile12Join03_0002Claim :=
  profile12Join02_0004Bound.glue profile12Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
