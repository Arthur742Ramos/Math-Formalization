/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join02_0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile10Join02_0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile10Join03_0002Claim : IntegralClaim := ⟨(9289/14276 : ℚ), (4059/4096 : ℚ), 991613033275618437608768456058⟩

theorem profile10Join03_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨10, by decide⟩) (2*approximationError) profile10Join03_0002Claim :=
  profile10Join02_0004Bound.glue profile10Join02_0005Bound (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
