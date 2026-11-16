/-
Generated exact integral certificates. Generation is untrusted;
all arithmetic and source binding are checked in Lean.
-/
module

public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0004
public import ErdosOverlap.Certificate.FrontierLeaves.Profile08Block0005

namespace ErdosOverlap.FrontierLeaves
open Numerics
@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false

def profile08Join00_0002Claim : IntegralClaim := ⟨(4749/1048576 : ℚ), (1871/262144 : ℚ), 0⟩

theorem profile08Join00_0002Bound : IntegralClaim.LowerCertificate (profileIntegrand ⟨8, by decide⟩) (2*approximationError) profile08Join00_0002Claim :=
  profile08Block0004.glue profile08Block0005 (by decide +kernel)

end
end ErdosOverlap.FrontierLeaves
