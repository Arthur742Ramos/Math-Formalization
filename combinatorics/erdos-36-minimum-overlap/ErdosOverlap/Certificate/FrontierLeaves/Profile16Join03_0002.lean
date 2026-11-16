/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile16Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile16Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (260195/262144 : ℚ), 991411498021680976446109832747⟩

theorem profile16Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨16, by decide⟩) (2*approximationError) profile16Join03_0002Claim :=
  profile16Join02_0004Bound.glue profile16Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
